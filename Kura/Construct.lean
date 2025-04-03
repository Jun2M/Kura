import Kura.Basic

namespace Graph
variable {α β : Type*}

def Edgeless (V : Set α) : Graph α β where
  V := V
  E := ∅
  Inc v e := false
  vx_mem_of_inc := by tauto
  edge_mem_of_inc := by tauto
  exists_vertex_inc := by tauto
  not_hypergraph := by tauto

end Graph
