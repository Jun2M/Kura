import Kura.Operation.Minor2
import Kura.Operation.Simple

open Set Function
variable {α ε α' α'' ε' : Type*} {u v w x y z : Set α} {e f : Sym2 (Set α)}
  {G H : Graph (Set α) (Sym2 (Set α))} {G' H' : Graph (Set α') (Sym2 (Set α'))} {u' v' w' : Set α'}

namespace Graph

@[simps!?]
def SimpMinor (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) : Graph (Set α) (Sym2 (Set α)) :=
  G / C |>.Simplify

#print Graph.SimpMinor_inc₂

theorem simpMinor_inc₂ (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    (G.SimpMinor C).Inc₂ e x y ↔ (G / C).Adj x y ∧ x ≠ y ∧ e = s(x, y) := by
  rw [SimpMinor_inc₂, ← and_assoc (b := x ≠ y), and_congr_left_iff]
  rintro rfl
  simp only [toSym2_eq_pair_iff, SetContract_inc₂, exists_and_left, exists_prop,
    Sym2.isDiag_iff_proj_eq, ne_eq, and_congr_left_iff]
  rintro hne
  refine ⟨fun ⟨s, hsC, ⟨hs, _⟩, u, v, hbtw, hx, hy⟩ ↦ ?_, fun ⟨e, hbtw⟩ ↦ ?_⟩
  · use s
    rw [← hx, ← hy]
    simp only [SetContract_inc₂, hsC, not_false_eq_true, true_and]
    use u, v, hbtw
  · have := hbtw.edge_mem.1
    simp at this
    rw [SetContract_inc₂] at hbtw
    exact ⟨e, hbtw.1, ⟨this, hbtw.1⟩, hbtw.2⟩

theorem simpMinor_adj (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    (G.SimpMinor C).Adj x y ↔ (G / C).Adj x y ∧ x ≠ y := by
  simp_rw [Adj, simpMinor_inc₂, ← and_assoc]
  rw [exists_eq_right, ← Graph.Adj]

instance simpMinor_isSimpleCanonical (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    IsSimpleCanonical (G.SimpMinor C) where
  loopless x := by
    simp only [simpMinor_adj, ne_eq, not_true_eq_false, and_false, not_false_eq_true]
  no_multi_edges e f he hf h := by
    induction' e with u v
    induction' f with x y
    simp only [SimpMinor_edgeSet, mem_setOf_eq, toSym2_eq_pair_iff, SetContract_inc₂,
      exists_and_left, exists_prop, Sym2.isDiag_iff_proj_eq] at he hf
    obtain ⟨he, he'⟩ := he

end Graph
