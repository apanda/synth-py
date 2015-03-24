class ACL(object):
  """Represent a single ACL"""
  def __init__ (self, grant, portmin, portmax = None):
    if not portmax:
      portmax = portmin
    self.grant = grant
    self.portmin = portmin
    self.portmax = portmax

  def allowsPort (self, port):
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

  def allowsInboundConnection (group, port):
    return any(map(lambda acl: acl.allowsConnection(group, port), self.inbound))

  def allowsOutboundConnection (group, port):
    return any(map(lambda acl: acl.allowsConnection(group, port), self.outbound))
  
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
    self.secgroups.append(\
        SecurityGroup(SecurityGroup.world, \
          [(SecurityGroup.world, 1, 65535)],\
          [(SecurityGroup.world, 1, 65535)]))
    self.instances = map(lambda i: Instance(*i), instances)
    self.secgroup_map = {sg.name: sg for sg in self.secgroups}
    self.instance_map = {vm.name: vm.group for vm in self.instances}
    self.instance_per_sg = {}
    for instance in self.instances:
      self.instance_per_sg[instance.group] = self.instance_per_sg.get(instance.group, 0) + 1

  def __repr__ (self):
    return "Security groups: \n\t%s\n Instances: \n\t%s"%('\n\t'.join(map(str, self.secgroups)), \
        '\n\t'.join(map(str, self.instances)))

  def acls_allow_connection (self, sg, port, acls):
    return any(map(lambda a: a.allowsConnection(sg, port), acls))

  def connection_allowed_secgroups (self, srcSG, destSG, port):
    outbound_allowed = self.acls_allow_connection(destSG, port, self.secgroup_map[srcSG].outbound)
    inbound_allowed = self.acls_allow_connection(srcSG, port, self.secgroup_map[destSG].inbound) 
    return (outbound_allowed and inbound_allowed)

  def groups_with_access (self, target, port):
    inboundPossible = filter(lambda a: a.allowsPort(port), self.secgroup_map[target].inbound)
    outboundSG = map(lambda a: self.secgroup_map[a.grant], inboundPossible)
    groups = filter(lambda a: self.acls_allow_connection(target, port, a.outbound), outboundSG)
    return map(lambda sg: sg.name, groups)

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
        others = self.groups_with_access(destSG, port)
        others = filter(lambda a: a not in explored and (self.instance_per_sg.get(a, 0) > 0), others)
        to_explore.extend(others)
    return False

  def direct_connection_fix (self, src, dest, port):
    if self.direct_connection_allowed(src, dest, port):
      return [] # Don't need to fix anything.
    else:
      # Find each of them
      srcSG = self.instance_map.get(src, SecurityGroup.world)
      destSG = self.instance_map.get(dest, SecurityGroup.world)
      outbound_allowed = self.acls_allow_connection(destSG, port, self.secgroup_map[srcSG].outbound)
      inbound_allowed = self.acls_allow_connection(srcSG, port, self.secgroup_map[destSG].inbound) 
      fix = []
      if not outbound_allowed:
        fix.append((srcSG, "outbound", ACL(destSG, port)))
      if not inbound_allowed:
        fix.append((destSG, "inbound", ACL(srcSG, port)))
      # Only one fix in this case, no choosing of what is better
      return [fix]

  def indirect_connection_fix (self, src, dest, port):
    """Check if this configuration allows indirect connection (i.e. can we chain together machines, using the same 
    protocol) on a particular port between a source and destination. A machine name that is not a valid instance is 
    treated as being outside the datacenter"""
    srcSG = self.instance_map.get(src, SecurityGroup.world)
    destSG = self.instance_map.get(dest, SecurityGroup.world)
    to_explore = [destSG]
    explored = set()
    fixes = []
    while to_explore:
      destSG = to_explore.pop()
      if destSG in explored:
        continue
      elif self.connection_allowed_secgroups(srcSG, destSG, port):
        return []
      else:
        explored.add(destSG)
        others = self.groups_with_access(destSG, port)
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
        print destSG, others
    return fixes

test_config = \
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
