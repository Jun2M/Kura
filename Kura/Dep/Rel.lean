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
  DecidableRel (ReflTransGen r) := by
  rintro a b
  -- obtain ⟨n, hn⟩ := List.exists_chain_of_relationReflTransGen
  sorry

def ReflClosure {α : Type*} : ClosureOperator (α → α → Prop) where
  toFun := ReflGen
  monotone' _ _ h _ _ h' := ReflGen.mono h h'
  le_closure' _ _ _ := ReflGen.single
  idempotent' _ := by
    ext a b
    constructor <;> rintro (h' | h')
    · exact ReflGen.refl
    · exact h'
    · exact ReflGen.refl
    · exact ReflGen.single (ReflGen.single h')

def TransClosure {α : Type*} : ClosureOperator (α → α → Prop) where
  toFun := TransGen
  monotone' _ _ h _ _ h' := TransGen.mono h h'
  le_closure' _ _ _ := TransGen.single
  idempotent' _ := by
    ext a b
    constructor <;> intro h
    · induction h with
      | single h => exact h
      | tail _ h' ih => exact TransGen.trans ih h'
    · exact TransGen.single h

def ReflTransClosure {α : Type*} : ClosureOperator (α → α → Prop) where
  toFun := ReflTransGen
  monotone' _ _ h _ _ h' := ReflTransGen.mono h h'
  le_closure' _ _ _ := ReflTransGen.single
  idempotent' _ := by
    ext a b
    constructor <;> intro h
    · induction h with
      | refl => exact ReflTransGen.refl
      | tail _ h' ih => exact ReflTransGen.trans ih h'
    · exact ReflTransGen.single h

def EqvGenClosure {α : Type*} : ClosureOperator (α → α → Prop) where
  toFun := EqvGen
  monotone' _ _ h _ _ h' := EqvGen.mono h h'
  le_closure' _ a b := EqvGen.rel a b
  idempotent' _ := by
    ext a b
    constructor <;> intro h
    · induction h with
      | rel _ _ h => exact h
      | refl => exact EqvGen.refl _
      | symm x y _ ih => exact EqvGen.symm x y ih
      | trans x y z _ _ ihxy ihyz => exact EqvGen.trans x y z ihxy ihyz
    · exact EqvGen.rel a b h



end Relation
