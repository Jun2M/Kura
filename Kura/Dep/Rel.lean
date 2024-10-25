import Mathlib.Order.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Quotient
import Mathlib.Order.Rel.GaloisConnection
import Mathlib.Order.Closure


lemma Irreflexive.ne_of_rel {α : Type u} {r : α → α → Prop} (h : Irreflexive r) {x y : α} (hxy : r x y) :
    x ≠ y := by
  intro hxy'
  subst hxy'
  exact h x hxy

namespace Relation

instance ReflTransGenDeciable {α : Type*} {r : α → α → Prop} [Fintype α] [DecidableRel r] :
  DecidableRel (Relation.ReflTransGen r) := by
  rintro a b
  -- obtain ⟨n, hn⟩ := List.exists_chain_of_relationReflTransGen
  sorry

instance instRelPreorder {α : Type*} : Preorder (α → α → Prop) where
  le r s := ∀ a b, r a b → s a b
  le_refl r := λ a b h => h
  le_trans r s t h1 h2 a b h := h2 a b (h1 a b h)


def ReflClosure {α : Type*} : ClosureOperator (α → α → Prop) where
  toFun := Relation.ReflGen
  monotone' r s h a b h' := Relation.ReflGen.mono h h'
  le_closure' r a b := Relation.ReflGen.single
  idempotent' r := by
    ext a b
    constructor <;> rintro (h' | h')
    · exact Relation.ReflGen.refl
    · exact h'
    · exact Relation.ReflGen.refl
    · exact Relation.ReflGen.single (Relation.ReflGen.single h')

def TransClosure {α : Type*} : ClosureOperator (α → α → Prop) where
  toFun := Relation.TransGen
  monotone' r s h a b h' := Relation.TransGen.mono h h'
  le_closure' r a b := Relation.TransGen.single
  idempotent' r := by
    ext a b
    constructor <;> intro h
    · induction h with
      | single h => exact h
      | tail _h h' ih => exact TransGen.trans ih h'
    · exact TransGen.single h

def ReflTransClosure {α : Type*} : ClosureOperator (α → α → Prop) where
  toFun := Relation.ReflTransGen
  monotone' r s h a b h' := Relation.ReflTransGen.mono h h'
  le_closure' r a b  := ReflTransGen.single
  idempotent' r := by
    ext a b
    constructor <;> intro h
    · induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _h h' ih => exact Relation.ReflTransGen.trans ih h'
    · exact ReflTransGen.single h
