import Mathlib.Tactic

def F {α : Type*} : α → ℕ := fun _ => 0

example : F 0 = 0 := rfl
example : F ℕ = 0 := rfl
example : F (0 : ℕ) = F (Type 1) := rfl

example (F : ∀ {α : Type*}, α → ℕ) : F 0 = F (Type 1) := by sorry
