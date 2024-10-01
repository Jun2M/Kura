import Kura.Searchable.Finite
import Kura.Planarity.Plainarity
import Kura.Conn.Minor

namespace Graph
open edge Sym2

lemma CompleteGraph5_not_Planar :
    ¬ Planar_by_AbstractDual (CompleteGraph 5) := by
  intro h
  obtain ⟨H, fE, hcm, hmc⟩ := h.exists_dual
  sorry

lemma CompleteBipGraph33_not_Planar :
    ¬ Planar_by_AbstractDual (CompleteBipGraph 3 3) := by
  sorry

theorem KuraCore {V E : Type*} [LinearOrder V] [Fintype V] (G : Graph V E) [Undirected G] [NConnected G 3]
  (hG5 : ¬ hasMinor G (CompleteGraph 5)) (hG33 : ¬ hasMinor G (CompleteBipGraph 3 3)) :
    Planar_by_AbstractDual G := by
  sorry

theorem Kuratowski_AbstractDual {V E : Type*} [LinearOrder V] [Fintype V] (G : Graph V E) [Undirected G] :
  Planar_by_AbstractDual G ↔ ¬ G.hasMinor (CompleteGraph 5) ∧ ¬ G.hasMinor (CompleteBipGraph 3 3) := by

  sorry
