import Kura.Operation.Minor2
import Kura.Operation.Simple

open Set Function
variable {α β α' α'' β' : Type*} {u v w x y z : Set α} {e f : Sym2 (Set α)}
  {G H : Graph (Set α) (Sym2 (Set α))} {G' H' : Graph (Set α') (Sym2 (Set α'))} {u' v' w' : Set α'}

namespace Graph

@[simps!]
def SimpMinor (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) : Graph (Set α) (Sym2 (Set α)) :=
  G / C |>.simplify

scoped infix:50 " // " => Graph.SimpMinor

#print Graph.SimpMinor_inc₂

theorem simpMinor_inc₂ (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    (G // C).Inc₂ e x y ↔ x ≠ y ∧ (G / C).Adj x y  ∧ e = s(x, y) := by
  rw [SimpMinor_inc₂, ← and_assoc (a := x ≠ y), and_congr_left_iff]
  rintro rfl
  simp only [toSym2_eq_pair_iff, SetContract_inc₂, exists_and_left, exists_prop,
    Sym2.isDiag_iff_proj_eq, ne_eq, and_congr_right_iff]
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
    (G // C).Adj x y ↔ x ≠ y ∧ (G / C).Adj x y := by
  simp_rw [Adj, simpMinor_inc₂, ← and_assoc]
  rw [exists_eq_right, ← Graph.Adj]

instance simpMinor_isSimpleCanonical (G : Graph (Set α) (Sym2 (Set α))) (C : Set (Sym2 (Set α))) :
    SimpleCanonical (G // C) := instSimpleCanonicalSimplify



end Graph
