import Mathlib.Data.Vector.Basic
import Mathlib.Data.Sym.Basic

open Mathlib

def EquivVectorone {α : Type*} : Vector α 1 ≃ α where
  toFun := (·.head)
  invFun := (⟨[·], rfl⟩)
  left_inv := fun v => by
    simp
    apply Vector.eq
    simp only [Vector.toList_singleton, List.cons.injEq, and_true]
    rfl
  right_inv := fun a => rfl
