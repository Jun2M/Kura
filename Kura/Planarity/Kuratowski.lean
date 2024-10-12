import Kura.Searchable.Finite
import Kura.Planarity.Plainarity
import Kura.Dep.Toss


namespace Graph
open edge Sym2


lemma CompleteGraph5_not_Planar :
    IsEmpty <| Planar_by_AbstractDual (CompleteGraph 5) := by
  by_contra! h
  simp only [not_isEmpty_iff] at h
  obtain ⟨planar⟩ := h
  let G := CompleteGraph 5
  let l := Fintype.card G.Faces

  have h1 : l * 3 ≤ 2 * 10 := by
    refine (Nat.mul_le_mul_left l G.three_le_dualGraph_minDegree).trans ?_
    convert G.dualGraph.n_minDegree_le_two_m

  have hEuler : 5 + l - 10 = 2 := EulerFormula G
  rw [Nat.sub_toss_eq' (by omega), Nat.toss_add_eq (by omega)] at hEuler
  rw [hEuler] at h1; clear hEuler
  omega


lemma CompleteBipGraph33_not_Planar :
    IsEmpty <| Planar_by_AbstractDual (CompleteBipGraph 3 3) := by
  by_contra! h
  simp only [not_isEmpty_iff] at h
  obtain ⟨planar⟩ := h
  let G := CompleteBipGraph 3 3
  let l := Fintype.card G.Faces

  have h1 : l * 4 ≤ 2 * 9 := by
    refine (Nat.mul_le_mul_left l G.four_le_dualGraph_minDegree_of_bipartite).trans ?_
    convert G.dualGraph.n_minDegree_le_two_m

  have hEuler : 6 + l - 9 = 2 := EulerFormula G
  rw [Nat.sub_toss_eq' (by omega), Nat.toss_add_eq (by omega)] at hEuler
  rw [hEuler] at h1; clear hEuler
  omega

-- theorem KuraCore {V E : Type*} [LinearOrder V] [Fintype V] (G : Graph V E) [Undirected G] [NConnected G 3]
--   (hG5 : ¬ hasMinor G (CompleteGraph 5)) (hG33 : ¬ hasMinor G (CompleteBipGraph 3 3)) :
--     Planar_by_AbstractDual G := by
--   sorry

-- theorem Kuratowski_AbstractDual {V E : Type*} [LinearOrder V] [Fintype V] (G : Graph V E) [Undirected G] :
--   Planar_by_AbstractDual G ↔ ¬ G.hasMinor (CompleteGraph 5) ∧ ¬ G.hasMinor (CompleteBipGraph 3 3) := by

  -- sorry
