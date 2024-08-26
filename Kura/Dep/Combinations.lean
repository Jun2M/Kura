import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Nat.Choose.Basic



theorem Sym.coe_mk_eq {α : Type*} (s : Sym α n) : ⟨↑s, by simp⟩ = s := by
  cases s
  rfl

@[simp]
theorem Sym.empty_toMultiset {α : Type*} : (∅ : Sym α 0).toMultiset = ∅ := by rfl

