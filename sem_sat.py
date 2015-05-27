import networkx as nx
from itertools import combinations
from sem import *
import z3

def process_configuration (configuration, port):
  """For now this just focuses on one port, will worry about ports later (actually multiple ports could probably just
  be done by first running one port at a time then optimizing to combine into ranges"""
  # Get all security groups
  secgroup_all = configuration.secgroup_map.keys()
  # Create a finite type over security groups
  sg_node, sg_nodes = z3.EnumSort ("sg", secgroup_all)
  nodes = dict(zip(secgroup_all, sg_nodes))
  # Two reachability function: d_reach is for immediate reachability, reach is for indirect reachabilty.
  d_reach = z3.Function('d_reach', sg_node, sg_node, z3.BoolSort())
  reach = z3.Function('reach', sg_node, sg_node, z3.BoolSort())

  # Some axioms for what is allowed
  axioms = []
  sg1 = z3.Const('s1', sg_node)
  sg2 = z3.Const('s2', sg_node)
  sg3 = z3.Const('s3', sg_node)
  previously_unallowed = []
  
  axioms.append(z3.ForAll([sg1], z3.Not(d_reach(sg1, sg1))))
  #axioms.append(z3.ForAll([sg1], z3.Not(reach(sg1, sg1))))
  ## Closure
  max_hops = len(secgroup_all) + 1
  closure_properties = []
  for i in xrange(0, max_hops):
    temp = [z3.Const('s_%d'%j, sg_node) for j in xrange(i)]
    vals = list(temp)
    temp.append(sg2)
    temp = [sg1] + temp
    path = map(lambda (a, b): d_reach(a, b), zip(temp, temp[1:]))
    print path
    if vals:
      closure_properties.append(z3.Exists(vals, z3.And(path)))
    else:
      closure_properties.append(z3.And(path))

  axioms.append(z3.ForAll([sg1, sg2], z3.Implies(reach(sg1, sg2), \
      z3.Or(sg1 == sg2, \
            *closure_properties))))
  axioms.append(z3.ForAll([sg1, sg2, sg3], z3.Implies(z3.And(reach(sg1, sg2), reach(sg2, sg3)),\
                                                       reach(sg1, sg3))))
  axioms.append(z3.ForAll([sg1, sg2], z3.Implies(d_reach(sg1, sg2), reach(sg1, sg2))))
  axioms.append(z3.ForAll([sg1], reach(sg1, sg1)))
  axioms.append(z3.ForAll([sg1], z3.Or(map(lambda s: sg1 == s, sg_nodes))))

  # Look at the combination of things that are or are not allowed.
  for (s1, s2) in combinations(secgroup_all, 2):
    if configuration.connection_allowed_secgroups(s1, s2, port): 
      axioms.append(d_reach(nodes[s1], nodes[s2])) 
    else:
      previously_unallowed.append((s1, s2))
    if configuration.connection_allowed_secgroups(s2, s1, port): 
      axioms.append(d_reach(nodes[s2], nodes[s1])) 
    else:
      previously_unallowed.append((s2, s1))
  solver = z3.Solver()
  solver.append(axioms)
  class SolverInstance (object):
    """ The object returned after processing the configuration that can be queried to find solutions"""
    def __init__(self):
      self.solver = solver
      self.nodes = nodes
      self.reach = reach
      self.d_reach = d_reach
      self.axioms = axioms
      self.port = port
      self.solver.push()
      self.configuration = configuration
      self.previously_unallowed = previously_unallowed

    def reset_new_conditions (self):
      """Forget about any of the requirements specified thus far"""
      self.solver.pop()
      self.solver.push()

    def require_direct_connection (self, sg1, sg2):
      """Require that the configuration allows direct connection between two groups"""
      self.solver.append(self.d_reach(self.nodes[sg1], self.nodes[sg2]))

    def require_indirect_connection (self, sg1, sg2):
      """Require that their exist some path that allows connectivity between two groups"""
      self.solver.append(self.reach(self.nodes[sg1], self.nodes[sg2]))

    def disallow_direct_connection (self, sg1, sg2):
      """Disallow any form of direct connectivity between two security groups"""
      self.solver.append(z3.Not(self.d_reach(self.nodes[sg1], self.nodes[sg2])))

    def disallow_indirect_connection (self, sg1, sg2):
      """Disallow indirect connectivity, i.e., make sure there is no indirect reachability"""
      self.solver.append(z3.Not(self.reach(self.nodes[sg1], self.nodes[sg2])))
    
    def disallow_new_direct_inbound_connections (self, sg):
      """Disallow any new direct connections to this security group (basically don't consider solutions where one would
      allow new connections to this group"""
      consider = filter(lambda (a, b): b == sg, self.previously_unallowed)
      for (a, b) in consider:
        self.disallow_direct_connection(a, b)
    
    def disallow_new_indirect_inbound_connections (self, sg):
      """Disallow any new indirect connections to this security group (basically don't consider solutions where one 
      would allow new connections to this group"""
      consider = filter(lambda (a, b): b == sg, self.previously_unallowed)
      for (a, b) in consider:
        self.disallow_indirect_connection(a, b)
    
    def disallow_new_direct_outbound_connections (self, sg):
      consider = filter(lambda (a, b): a == sg, self.previously_unallowed)
      for (a, b) in consider:
        self.disallow_direct_connection(a, b)
    
    def disallow_new_indirect_outbound_connections (self, sg):
      consider = filter(lambda (a, b): a == sg, self.previously_unallowed)
      for (a, b) in consider:
        self.disallow_indirect_connection(a, b)

    def disallow_all_new (self):
      for (a, b) in self.previously_unallowed:
        self.disallow_direct_connection(a, b)

    def check_and_interpret (self):
      """Synthesize configuration based on current parameters"""
      result = self.solver.check()
      if result != z3.sat:
        print "Failed to check" # Really in this case we should be extracting the unsat core and trying to figure out
                                # what is conflicting. This seems useful for users (also maybe allows us to deal with
                                # deletions).
        return
      model = self.solver.model()
      fixes = []
      for (sg1, sg2) in self.previously_unallowed:
        if z3.is_true(model.evaluate(self.d_reach(self.nodes[sg1], self.nodes[sg2]))):
          print "Result will connect %s ---> %s directly"%(sg1, sg2)
          fixes.append(self.configuration.direct_connection_fix_sg(sg1, sg2, self.port))
      print "Fix is thus\n\t%s"%('\n\t'.join(map(str, fixes)))

  return SolverInstance()
