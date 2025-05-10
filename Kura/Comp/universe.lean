import Mathlib.Tactic

def F {α : Type*} : α → ℕ := fun _ => 0

example : F 0 = 0 := rfl
example : F ℕ = 0 := rfl
example : F (0 : ℕ) = F (Type 1) := rfl

example (F : ∀ {α : _}, α → ℕ) : F (0 : ℕ) = 0 := by sorry
example (F : ∀ {α : _}, α → ℕ) : F ℕ = 0 := by sorry
example (F : ∀ {α : _}, α → ℕ) : F (0 : ℕ) = F (Type 1) := by sorry


universe v u₀ u₁ v₀ v₁ v₂ w w₀ w₁

class VertexTypeULiftable (f : outParam (Type u₀ → Prop)) (g : Type v₀ → Prop) where
  congr {α β} : α ≃ β → f α ↔ g β

class Const (f : ∀ {α : _}, α → Prop) where
  const {α β} : f α ↔ f β
