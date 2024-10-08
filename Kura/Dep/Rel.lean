import Mathlib.Order.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Quotient


lemma Irreflexive.ne_of_rel {α : Type u} {r : α → α → Prop} (h : Irreflexive r) {x y : α} (hxy : r x y) :
    x ≠ y := by
  intro hxy'
  subst hxy'
  exact h x hxy



instance Relation.ReflTransGenDeciable {α : Type*} {r : α → α → Prop} [Fintype α] [DecidableRel r] :
  DecidableRel (Relation.ReflTransGen r) := by
  rintro a b
  -- obtain ⟨n, hn⟩ := List.exists_chain_of_relationReflTransGen
  sorry
