import networkx as nx
from itertools import combinations
class ACL(object):
  """Represent a single ACL"""
  def __init__ (self, grant, portmin, portmax = None):
    if not portmax:
      portmax = portmin
    self.grant = grant
    self.portmin = portmin
    self.portmax = portmax

  def allowsPort (self, port):
    """ Does this ACL allow a particular port through"""
    return ((self.portmin <= port) and (port <= self.portmax))

  def allowsConnection (self, group, port):
    return (((self.grant == SecurityGroup.world) or (self.grant == group)) and self.allowsPort(port))

  def __repr__ (self):
    return "%s %d -- %d"%(self.grant, self.portmin, self.portmax)

class SecurityGroup(object):
  """Represents a security group"""
  world = "any" # A security globe for the world
  def __init__ (self, name, inbound, outbound):
    self.name = name
    self.inbound = map(lambda i: ACL(*i), inbound)
    self.outbound = map(lambda i: ACL(*i), outbound)

  def allowsInboundConnection (self, group, port):
    """Does this security group allow inbound connection from group and port"""
    return any(map(lambda acl: acl.allowsConnection(group, port), self.inbound))

  def allowsOutboundConnection (self, group, port):
    """Does this security group allow outbound connection to group and port"""
    return any(map(lambda acl: acl.allowsConnection(group, port), self.outbound))
  
  def allowsInboundPort (self, port):
    """Does this security group allow inbound connection on port"""
    return any(map(lambda acl: acl.allowsPort(port), self.inbound))

  def allowsOutboundConnection (self, group, port):
    """Does this security group allow outbound connection to group and port"""
    return any(map(lambda acl: acl.allowsConnection(group, port), self.outbound))

  def allowsOutboundPort (self, port):
    """Does this security group allow outbound connection on port"""
    return any(map(lambda acl: acl.allowsPort(port), self.outbound))

  def __repr__ (self):
    return "%s <<Inbound>> [%s] <<Outbound>> [%s]"%(self.name, ' '.join(map(str, self.inbound)), \
        ' '.join(map(str, self.outbound)))

class Instance(object):
  """An instance"""
  def __init__ (self, name, group):
    self.name = name
    self.group = group
  def __repr__ (self):
    return "%s -> %s"%(self.name, self.group)

class Configuration(object):
  """An entire configuration"""
  def __init__ (self, securitygroups, instances):
    self.secgroups = map(lambda i: SecurityGroup(*i), securitygroups)
    #self.secgroups.append(\
        #SecurityGroup(SecurityGroup.world, \
          #[(SecurityGroup.world, 1, 65535)],\
          #[(SecurityGroup.world, 1, 65535)]))
    self.instances = map(lambda i: Instance(*i), instances)
    self.secgroup_map = {sg.name: sg for sg in self.secgroups}
    self.instance_map = {vm.name: vm.group for vm in self.instances}
    self.instance_per_sg = {}
    for instance in self.instances:
      self.instance_per_sg[instance.group] = self.instance_per_sg.get(instance.group, 0) + 1
    self.instance_per_sg[SecurityGroup.world] = float("inf") # Overkill
  def __repr__ (self):
    return "Security groups: \n\t%s\n Instances: \n\t%s\n Security Group weights: \n\t%s"%\
        ('\n\t'.join(map(str, self.secgroups)), \
        '\n\t'.join(map(str, self.instances)),\
        '\n\t'.join(map(lambda (a, b): '%s %s'%(a, str(b)), self.instance_per_sg.items())))

  def acls_allow_connection (self, sg, port, acls):
    return any(map(lambda a: a.allowsConnection(sg, port), acls))

  def connection_allowed_secgroups (self, srcSG, destSG, port):
    """Can two security groups talk to each other over a specific port"""
    outbound_allowed = self.secgroup_map[srcSG].allowsOutboundConnection(destSG, port)
    inbound_allowed = self.secgroup_map[destSG].allowsInboundConnection(srcSG, port)
    return (outbound_allowed and inbound_allowed)

  def groups_with_inbound_access (self, target, port):
    """Find all groups that can connect to target at port"""
    # Get a list of all security groups from which target would accept connection at port.
    if target is SecurityGroup.world:
      inboundPossible = map(lambda a: ACL(a, 1, 65535), self.secgroup_map.keys())
    else:
      inboundPossible = filter(lambda a: a.allowsPort(port), self.secgroup_map[target].inbound)
    # Get the subset of the above that allow outbound connections to the target group at port.
    groups = filter(lambda a: self.secgroup_map[a.grant].allowsOutboundConnection(target, port), inboundPossible)
    return map(lambda acl: acl.grant, groups)

  def groups_with_outbound_access (self, src, port):
    """Find all groups that src can connect to at port"""
    # Get a list of all ports to which source can connect
    if src is SecurityGroup.world:
      outboundPossible = map(lambda a: ACL(a, 1, 65535), self.secgroup_map.keys())
    else:
      outboundPossible = filter(lambda a: a.allowsPort(port), self.secgroup_map[src].outbound)
    # Find those that allow connection
    groups = filter(lambda a: self.secgroup_map[a.grant].allowsInboundConnection(src, port), outboundPossible)
    return map(lambda acl: acl.grant, groups)

  def direct_connection_allowed (self, src, dest, port):
    """Check if this configuration allows direct connection on a particular port between a source and destination. A
    machine name that is not a valid instance is treated as being outside the datacenter"""
    srcSG = self.instance_map.get(src, SecurityGroup.world)
    destSG = self.instance_map.get(dest, SecurityGroup.world)
    return self.connection_allowed_secgroups(srcSG, destSG, port)


  def indirect_connection_allowed (self, src, dest, port):
    """Check if this configuration allows indirect connection (i.e. can we chain together machines, using the same 
    protocol) on a particular port between a source and destination. A machine name that is not a valid instance is 
    treated as being outside the datacenter"""
    srcSG = self.instance_map.get(src, SecurityGroup.world)
    destSG = self.instance_map.get(dest, SecurityGroup.world)
    to_explore = [destSG]
    explored = set()
    while to_explore:
      destSG = to_explore.pop()
      if destSG in explored:
        continue
      elif self.connection_allowed_secgroups(srcSG, destSG, port):
        return True
      else:
        explored.add(destSG)
        others = self.groups_with_inbound_access(destSG, port)
        others = filter(lambda a: a not in explored and (self.instance_per_sg.get(a, 0) > 0), others)
        to_explore.extend(others)
    return False

  def direct_connection_fix_sg (self, srcSG, destSG, port):
      outbound_allowed = self.acls_allow_connection(destSG, port, self.secgroup_map[srcSG].outbound)
      inbound_allowed = self.acls_allow_connection(srcSG, port, self.secgroup_map[destSG].inbound) 
      fix = []
      if not outbound_allowed:
        fix.append((srcSG, "outbound", ACL(destSG, port)))
      if not inbound_allowed:
        fix.append((destSG, "inbound", ACL(srcSG, port)))
      # Only one fix in this case, no choosing of what is better
      return fix

  def direct_connection_fix (self, src, dest, port):
    """Fix cases where VMs are not directly connected"""
    if self.direct_connection_allowed(src, dest, port):
      return [] # Don't need to fix anything.
    else:
      # Find each of them
      srcSG = self.instance_map.get(src, SecurityGroup.world)
      destSG = self.instance_map.get(dest, SecurityGroup.world)
      return [self.direct_connection_fix_sg(srcSG, destSG, port)]

  def fix_metric (self, fix):
    """Metric for goodness of fix. We are basically asking how many new machines can now directly connect to some SG
    because of this fix"""
    # No new connectivity
    if not fix:
      return 0
    # A fix only connects two groups, so is fine
    fix = fix[0]
    sg1 = fix[0]
    sg2 = fix[2].grant
    return max(self.instance_per_sg[sg1], self.instance_per_sg[sg2])

  def indirect_connection_fix_graph (self, src, dest, port):
    """Yaron's algorithm for incremental indirect connection fixing"""
    graph = nx.DiGraph()
    graph.add_nodes_from(self.secgroup_map.keys())
    for (sa, sb) in combinations(self.secgroup_map.keys(), 2):
      if self.instance_per_sg.get(sa, 0) == 0:
        continue
      if self.instance_per_sg.get(sb, 0) == 0:
        continue
      weight = max(self.instance_per_sg[sa], self.instance_per_sg[sb])
      if self.connection_allowed_secgroups(sa, sb, port):
        graph.add_edge(sa, sb, weight=0)
      else:
        graph.add_edge(sa, sb, weight = weight)

      if self.connection_allowed_secgroups(sb, sa, port):
        graph.add_edge(sb, sa, weight=0)
      else:
        graph.add_edge(sb, sa, weight = weight)
    srcSG = self.instance_map.get(src, SecurityGroup.world)
    destSG = self.instance_map.get(dest, SecurityGroup.world)
    paths = nx.all_shortest_paths(graph, srcSG, destSG, weight = "weight")
    edges = map(lambda l: zip(l, l[1:]), paths)
    weights = map(lambda l: map(lambda e: (e, graph.get_edge_data(*e)['weight']), l), edges)
    non_zero_edges = map(lambda l: filter(lambda (e, w): w > 0, l), weights)
    just_edges = map(lambda l: map(lambda (e, w): e, l), non_zero_edges)
    fixes = map(lambda l: map(lambda (e1, e2): self.direct_connection_fix_sg(e1, e2, port), l), just_edges)
    return non_zero_edges


  def indirect_connection_fix (self, src, dest, port):
    """Check if this configuration allows indirect connection (i.e. can we chain together machines, using the same 
    protocol) on a particular port between a source and destination. A machine name that is not a valid instance is 
    treated as being outside the datacenter"""
    srcSG = self.instance_map.get(src, SecurityGroup.world)
    destSG = self.instance_map.get(dest, SecurityGroup.world)
    origDestSG = destSG
    to_explore = [destSG]
    explored = set()
    fixes = []
    # Explore by changing the destination further away, the ideas is to take the transitive closure of all groups 
    # reachable from the destination and connect source to this.
    while to_explore:
      destSG = to_explore.pop()
      if destSG in explored:
        continue
      elif self.connection_allowed_secgroups(srcSG, destSG, port):
        return []
      else:
        explored.add(destSG)
        others = self.groups_with_inbound_access(destSG, port)
        others = filter(lambda a: a not in explored and (self.instance_per_sg.get(a, 0) > 0), others)
        outbound_allowed = self.acls_allow_connection(destSG, port, self.secgroup_map[srcSG].outbound)
        inbound_allowed = self.acls_allow_connection(srcSG, port, self.secgroup_map[destSG].inbound) 
        fix = []
        if not outbound_allowed:
          fix.append((srcSG, "outbound", ACL(destSG, port)))
        if not inbound_allowed:
          fix.append((destSG, "inbound", ACL(srcSG, port)))
        fixes.append(fix)
        to_explore.extend(others)
    destSG = origDestSG
    explored.clear()
    to_explore = self.groups_with_outbound_access(srcSG, port)
    explored.add(srcSG)

    ## Transitive closure from the source. Essentially find everything reachable from the source
    while to_explore:
      srcSG = to_explore.pop()
      if srcSG in explored:
        continue
      elif self.connection_allowed_secgroups(srcSG, destSG, port):
        return []
      else:
        explored.add(destSG)
        others = self.groups_with_outbound_access(srcSG, port)
        others = filter(lambda a: a not in explored and (self.instance_per_sg.get(a, 0) > 0), others)
        outbound_allowed = self.acls_allow_connection(destSG, port, self.secgroup_map[srcSG].outbound)
        inbound_allowed = self.acls_allow_connection(srcSG, port, self.secgroup_map[destSG].inbound) 
        fix = []
        if not outbound_allowed:
          fix.append((srcSG, "outbound", ACL(destSG, port)))
        if not inbound_allowed:
          fix.append((destSG, "inbound", ACL(srcSG, port)))
        fixes.append(fix)
        to_explore.extend(others)

    min_fix_length = min(map(self.fix_metric, fixes))
    
    filtered_fixes = filter(lambda c: len(c) == min_fix_length, fixes)
    return (fixes, filtered_fixes)

test_config1 = \
    Configuration(\
      [("frontend", 
         [("frontend", 1, 65535),
          ("any", 22)],
         [("frontend", 1, 65535),
          ("backend", 1, 65535)]),
       ("backend",
         [("backend", 1, 65535)],
         [("backend", 1, 65535),
          ("any", 22)])],
       [("a", "frontend"), ("b", "backend"), ("c", "backend")])

test_config2 = \
    Configuration(\
      [("frontend", 
         [("frontend", 1, 65535),
          ("any", 22)],
         [("frontend", 1, 65535),
          ("backend", 1, 65535)]),
       ("backend",
         [("backend", 1, 65535),
          ("frontend", 1, 65535)],
         [("backend", 1, 65535),
           ("any", 22)])],
       [("a", "frontend"), ("b", "backend"), ("c", "backend")])


test_config3 = \
    Configuration(\
     [("sg1",
       [("sg1", 1, 65535),
        ("sg2", 1, 65535)],
       [("sg1", 1, 65535)]),
      ("sg2",
        [("sg2", 1, 65535),
         ("sg3", 1, 65535)],
        [("sg1", 1, 65535),
         ("sg2", 1, 65535)]),
      ("sg3",
        [("any", 22),
         ("any", 80),
         ("sg3", 1, 65535)],
        [("sg2", 1, 65535),
         ("sg3", 1, 65535)])],
      [("a", "sg1"), ("b", "sg2"), ("c", "sg3")])

test_config4 = \
    Configuration(\
     [("sg1",
       [("sg1", 1, 65535),
        ("sg2", 1, 65535)],
       [("sg1", 1, 65535)]),
      ("sg2",
        [("sg2", 1, 65535),
         ("sg3", 1, 65535)],
        [("sg1", 1, 65535),
         ("sg2", 1, 65535)]),
      ("sg3",
        [("any", 22),
         ("any", 80),
         ("sg3", 1, 65535)],
        [("sg2", 1, 65535),
         ("sg3", 1, 65535)])],
      [("a", "sg1"), ("c", "sg3")])

test_config5 = \
    Configuration(\
     [("sg1",
       [("sg1", 1, 65535),
        ("sg2", 1, 65535)],
       [("sg1", 1, 65535)]),
      ("sg2",
        [("sg2", 1, 65535),
         ("sg3", 1, 65535)],
        [("sg1", 1, 65535),
         ("sg2", 1, 65535)]),
      ("sg3",
        [],
        [("sg2", 22)]),
      ("sg4",
        [("any", 22),
         ("any", 80),
         ("sg3", 1, 65535)],
        [("sg2", 1, 65535),
         ("sg3", 1, 65535)])],
      [("a", "sg1"), ("b", "sg2"), ("c", "sg3"), ("d", "sg4")])

test_config6 = \
    Configuration(\
     [("sg1",
       [("sg1", 1, 65535),
        ("sg2", 1, 65535)],
       [("sg1", 1, 65535),
         ("sg2", 1, 65535)]),
      ("sg2",
        [("sg1", 1, 65535),
          ("sg2", 1, 65535),
         ("sg3", 1, 65535)],
        [("sg1", 1, 65535),
         ("sg2", 1, 65535)]),
      ("sg3",
        [("sg4", 22)],
        [("sg4", 22)]),
      ("sg4",
        [("sg5", 22),
         ("sg5", 80),
         ("sg3", 1, 65535)],
        [("sg3", 1, 65535)]),
      ("sg5",
        [],
        [("sg4", 1, 65535)])],
      [("a", "sg1"), ("b", "sg2"), ("c", "sg3"), ("d", "sg4")])

test_config7 = \
    Configuration(
        [("a",
          [],
          [("b", 1, 65535)]),
         ("b",
           [("a", 1, 65535)],
           []),
         ("c",
           [],
           [("d", 1, 65535)]),
         ("d",
           [("c", 1, 65535)],
           []),
         ("e",
           [],
           [("f", 1, 65535)]),
         ("f",
           [("e", 1, 65535)],
           [])],
         [("m1", "a"), ("m2", "b"), ("m3", "c"), ("m4", "d"), ("m5", "e")])

if __name__ == "__main__":
  configs = [test_config1, test_config2, test_config3, test_config4, test_config5, test_config6]
  for config in configs:
    print config
    instances = map(lambda i: i.name, config.instances)
    instances.append("z")
    for (ia, ib) in combinations(instances, 2):
      print "Testing %s %s"%(ia, ib)
      if not config.indirect_connection_allowed(ia, ib, 22):
        print "Fix for %s %s is %s"%(ia, ib, "\n\t".join(map(str, config.indirect_connection_fix_graph(ia, ib, 22))))
      else:
        print "%s %s allowed"%(ia, ib)
