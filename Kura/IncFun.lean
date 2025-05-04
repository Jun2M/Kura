import Kura.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Set.Card
import Matroid.ForMathlib.Card

open Set

variable {α ε : Type*} {x y z u v w : α} {e f : ε} {G H : Graph α ε}

namespace Graph

/-- The set of ends of an edge `e`. -/
def endSet (G : Graph α ε) (e : ε) : Set α := {x | G.Inc e x}

@[simp]
lemma mem_endSet_iff : x ∈ G.endSet e ↔ G.Inc e x := Iff.rfl

lemma Inc₂.endSet_eq (h : G.Inc₂ e x y) : G.endSet e = {x,y} := by
  ext a
  simp only [mem_endSet_iff, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun h' ↦ h'.eq_or_eq_of_inc₂ h, ?_⟩
  rintro (rfl | rfl)
  · exact h.inc_left
  exact h.inc_right

lemma IsLoopAt.endSet_eq (h : G.IsLoopAt e x) : G.endSet e = {x} := by
  rw [Inc₂.endSet_eq h, pair_eq_singleton]

lemma endSet_eq_of_not_mem_edgeSet (he : e ∉ G.E) : G.endSet e = ∅ := by
  simp only [endSet, eq_empty_iff_forall_not_mem, mem_setOf_eq]
  exact fun x hx ↦ he hx.edge_mem

lemma endSet_encard_le (G : Graph α ε) (e : ε) : (G.endSet e).encard ≤ 2 := by
  by_cases heE : e ∈ G.E
  · obtain ⟨x, y, h⟩ := exists_inc₂_of_mem_edgeSet heE
    rw [h.endSet_eq]
    exact encard_pair_le x y
  simp [endSet_eq_of_not_mem_edgeSet heE]

@[simp]
lemma subsingleton_setOf_inc₂ (G : Graph α ε) (e : ε) (x : α) :
    {y | G.Inc₂ e x y}.Subsingleton := by
  simp only [Set.Subsingleton, mem_setOf_eq]
  exact fun y hy z hz ↦ hy.eq_of_inc₂ hz

@[simp]
lemma endSet_finite (G : Graph α ε) (e : ε) : (G.endSet e).Finite :=
  finite_of_encard_le_coe <| G.endSet_encard_le e
