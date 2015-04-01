import networkx as nx
from itertools import combinations
from sem import *
import z3

def process_configuration (configuration, port):
  """For now this just focuses on one port, worry about ports later."""
  secgroup_all = configuration.secgroup_map.keys()
  sg_node, sg_nodes = z3.EnumSort ("sg", secgroup_all)
  nodes = dict(zip(secgroup_all, sg_nodes))
  d_reach = z3.Function('d_reach', sg_node, sg_node, z3.BoolSort())
  reach = z3.Function('reach', sg_node, sg_node, z3.BoolSort())
  axioms = []
  sg1 = z3.Const('s1', sg_node)
  sg2 = z3.Const('s2', sg_node)
  sg3 = z3.Const('s3', sg_node)
  previously_unallowed = []
  
  # Always unreachable from self (not doing this breaks many things)
  axioms.append(z3.ForAll([sg1], z3.Not(d_reach(sg1, sg1))))
  axioms.append(z3.ForAll([sg1], z3.Not(reach(sg1, sg1))))
  # Closure
  axioms.append(z3.ForAll([sg1, sg2], reach(sg1, sg2) ==
      z3.Or(d_reach(sg1, sg2),\
        z3.Exists([sg3], \
          z3.And(reach(sg1, sg3),\
                 reach(sg3, sg2),
                 z3.Not(sg1 == sg2))))))
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
      self.solver.pop()
      self.solver.push()
    def require_direct_connection (self, sg1, sg2):
      self.solver.append(self.d_reach(self.nodes[sg1], self.nodes[sg2]))
    def require_indirect_connection (self, sg1, sg2):
      self.solver.append(self.reach(self.nodes[sg1], self.nodes[sg2]))
    def disallow_direct_connection (self, sg1, sg2):
      self.solver.append(z3.Not(self.d_reach(self.nodes[sg1], self.nodes[sg2])))
    def disallow_indirect_connection (self, sg1, sg2):
      self.solver.append(z3.Not(self.reach(self.nodes[sg1], self.nodes[sg2])))
    def disallow_new_direct_inbound_connections (self, sg):
      consider = filter(lambda (a, b): b == sg, self.previously_unallowed)
      for (a, b) in consider:
        self.disallow_direct_connection(a, b)
    def disallow_new_indirect_inbound_connections (self, sg):
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
    def check_and_interpret (self):
      result = self.solver.check()
      if result != z3.sat:
        print "Failed to check"
        return
      model = self.solver.model()
      fixes = []
      for (sg1, sg2) in self.previously_unallowed:
        if z3.is_true(model.evaluate(self.d_reach(self.nodes[sg1], self.nodes[sg2]))):
          print "Result will connect %s ---> %s directly"%(sg1, sg2)
          fixes.append(self.configuration.direct_connection_fix_sg(sg1, sg2, self.port))
      print "Fix is thus\n\t%s"%('\n\t'.join(map(str, fixes)))
  return SolverInstance()
