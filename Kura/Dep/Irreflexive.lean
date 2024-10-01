import Mathlib.Order.Defs


lemma Irreflexive.ne_of_rel {α : Type u} {r : α → α → Prop} (h : Irreflexive r) {x y : α} (hxy : r x y) :
    x ≠ y := by
  intro hxy'
  subst hxy'
  exact h x hxy
