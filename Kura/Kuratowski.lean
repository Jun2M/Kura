import Kura.Finite
import Kura.Plainarity

namespace Graph
open edge Sym2

theorem Kuratowski_AbstractDual {V E : Type*} [DecidableEq V] (G : Graph V E) [Undirected G] :
  Planar_by_AbstractDual G ↔ ¬ G.hasMinor (Complete (Fin 5)) ∧ ¬ G.hasMinor (BipComplete 3 3) := by
  
  sorry
