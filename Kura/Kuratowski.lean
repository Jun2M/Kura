import Kura.Searchable.Finite
import Kura.Planarity.Plainarity

namespace Graph
open edge Sym2

theorem Kuratowski_AbstractDual {V E : Type*} [LinearOrder V] [Fintype V] (G : Graph V E) [Undirected G] :
  Planar_by_AbstractDual G ↔ ¬ G.hasMinor (CompleteGraph 5) ∧ ¬ G.hasMinor (CompleteBipGraph 3 3) := by

  sorry
