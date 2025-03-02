import Kura.Basic


open Set Function
variable {α β γ δ ε ζ : Type*} {G₁ : Graph α β} {G₂ : Graph γ δ} {G₃ : Graph ε ζ} {a b c : α}
  {e f : β} {u v w : γ} {x y z : δ}
namespace Graph


structure HomSys (α β γ δ : Type*) where
  fᵥ : α → γ
  fₑ : β → δ

instance : CoeFun (HomSys α β γ δ) fun (_ : HomSys α β γ δ) ↦ α → γ where
  coe v := v.fᵥ

instance : CoeFun (HomSys α β γ δ) fun (_ : HomSys α β γ δ) ↦ β → δ where
  coe v := v.fₑ

def HomSys.id : HomSys α β α β where
  fᵥ := _root_.id
  fₑ := _root_.id

def HomSys.comp (g : HomSys α β γ δ) (f : HomSys γ δ ε ζ) : HomSys α β ε ζ where
  fᵥ := f.fᵥ ∘ g.fᵥ
  fₑ := f.fₑ ∘ g.fₑ

def HomSys.HomOn (f : HomSys α β γ δ) (G₁ : Graph α β) (G₂ : Graph γ δ) : Prop :=
  ∀ v e, G₁.Inc v e → G₂.Inc (f.fᵥ v) (f.fₑ e)

def HasHom (G₁ : Graph α β) (G₂ : Graph γ δ) := ∃ f : HomSys α β γ δ, f.HomOn G₁ G₂
