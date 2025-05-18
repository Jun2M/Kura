import Kura.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Set.Card
import Matroid.ForMathlib.Card

open Set

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β}

namespace Graph

/-- The set of ends of an edge `e`. -/
def endSet (G : Graph α β) (e : β) : Set α := {x | G.Inc e x}

@[simp]
lemma mem_endSet_iff : x ∈ G.endSet e ↔ G.Inc e x := Iff.rfl

lemma IsLink.endSet_eq (h : G.IsLink e x y) : G.endSet e = {x,y} := by
  ext a
  simp only [mem_endSet_iff, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun h' ↦ h'.eq_or_eq_of_isLink h, ?_⟩
  rintro (rfl | rfl)
  · exact h.inc_left
  exact h.inc_right

lemma IsLoopAt.endSet_eq (h : G.IsLoopAt e x) : G.endSet e = {x} := by
  rw [IsLink.endSet_eq h, pair_eq_singleton]

lemma endSet_eq_of_not_mem_edgeSet (he : e ∉ E(G)) : G.endSet e = ∅ := by
  simp only [endSet, eq_empty_iff_forall_not_mem, mem_setOf_eq]
  exact fun x hx ↦ he hx.edge_mem

lemma endSet_encard_le (G : Graph α β) (e : β) : (G.endSet e).encard ≤ 2 := by
  by_cases heE : e ∈ E(G)
  · obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet heE
    rw [h.endSet_eq]
    exact encard_pair_le x y
  simp [endSet_eq_of_not_mem_edgeSet heE]

@[simp]
lemma subsingleton_setOf_isLink (G : Graph α β) (e : β) (x : α) :
    {y | G.IsLink e x y}.Subsingleton := by
  simp only [Set.Subsingleton, mem_setOf_eq]
  exact fun y hy z hz ↦ hy.eq_of_isLink hz

@[simp]
lemma endSet_finite (G : Graph α β) (e : β) : (G.endSet e).Finite :=
  finite_of_encard_le_coe <| G.endSet_encard_le e
