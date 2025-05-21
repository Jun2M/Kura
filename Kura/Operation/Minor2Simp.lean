import Kura.Operation.Minor2
import Kura.Operation.Simple

open Set Function
variable {α β α' α'' β' : Type*} {u v w x y z : Set α} {e f : Sym2 (Set α)}
  {G H : Graph (Set α) (Sym2 (Set α))} {G' H' : Graph (Set α') (Sym2 (Set α'))} {u' v' w' : Set α'}

namespace Graph

@[simps! vertexSet edgeSet]
noncomputable def SimpMinor (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) : Graph (Set α) (Sym2 (Set α)) :=
  G / C |>.simplify

scoped infix:50 " // " => Graph.SimpMinor

@[simp]
theorem simpMinor_isLink (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    (G // C).IsLink e x y ↔  e = s(x, y) ∧ x ≠ y ∧ (G / C).Adj x y := by
  simp only [SimpMinor, isLink_iff_eq, Simplify_edgeSet, SetContract_edgeSet, mem_diff, mem_setOf_eq,
    Sym2.isDiag_iff_proj_eq, toSym2_eq_pair_iff, SetContract_isLink, exists_and_left, exists_prop,
    ne_eq]
  rw [and_congr_right_iff, and_congr_right_iff]
  rintro rfl hne
  refine ⟨fun ⟨s, hsC, ⟨hs, _⟩, u, hx, v, hy, hbtw⟩ ↦ ?_, fun ⟨e, hbtw⟩ ↦ ?_⟩
  · use s
    rw [← hx, ← hy]
    simp only [SetContract_isLink, hsC, not_false_eq_true, true_and]
    use u, rfl, v, rfl, hbtw
  · have := hbtw.edge_mem.1
    simp at this
    rw [SetContract_isLink] at hbtw
    exact ⟨e, hbtw.1, ⟨this, hbtw.1⟩, hbtw.2⟩

theorem simpMinor_adj (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    (G // C).Adj x y ↔ x ≠ y ∧ (G / C).Adj x y := by
  simp_rw [Adj, simpMinor_isLink]
  rw [exists_eq_left, ← Graph.Adj]

instance simpMinor_isSimpleCanonical (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    SimpleCanonical (G // C) := instSimpleCanonicalSimplify

lemma edgeSet_ncard_simpMinor_singleton (G : Graph (Set α) (Sym2 (Set α))) (s : Sym2 (Set α))
    [Finite E(G)] : (G // {s}).edgeSet.ncard = {e ∈ E(G) | ¬ G.parallel e s}.ncard := by

end Graph
