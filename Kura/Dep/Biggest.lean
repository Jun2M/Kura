import Mathlib.Tactic


def IsBiggest {α : Type*} [Preorder α] (P : α → Prop) (a : α) : Prop :=
  P a ∧ ∀ b, a < b → ¬ P b

def IsSmallest {α : Type*} [Preorder α] (P : α → Prop) (a : α) : Prop :=
  P a ∧ ∀ b, b < a → ¬ P b

