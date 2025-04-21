import Kura.Graph


open Set Function
variable {α β α' β' γ δ ε ζ : Type*} {G₁ : Graph α β} {G₂ : Graph γ δ} {G₃ : Graph ε ζ} {a b c : α}
  {e f : β} {u v w : γ} {x y z : δ}
namespace Graph


structure HomSys (α β α' β' : Type*) where
  toFun : α → α'
  edgeFun : β → β'

def HomSys.ofVxFun (f : α → α') : HomSys α β α' β where
  toFun := f
  edgeFun := id

instance : CoeFun (HomSys α β α' β') fun (_ : HomSys α β α' β') ↦ α → α' where
  coe v := v.toFun

-- structure HomSys.IsLawful (G : Graph α β) (f : HomSys α β γ δ) : Prop where
--   forall_foo : ∀ e x y, G.Inc₂ e x y →

def map (G : Graph α β) (f : HomSys α β α' β') : Graph α' β' where
  V := f '' G.V
  E := f.edgeFun '' G.E
  Inc x e := ∃ x₀ e₀, G.Inc x₀ e₀ ∧ x = f x₀ ∧ e = f.edgeFun e₀
  vx_mem_of_inc := sorry
  edge_mem_of_inc := sorry
  exists_vertex_inc := sorry
  not_hypergraph := sorry

-- instance : CoeFun (HomSys α β γ δ) fun (_ : HomSys α β γ δ) ↦ β → δ where
--   coe v := v.fₑ

def HomSys.id : HomSys α β α β where
  toFun := _root_.id
  edgeFun := _root_.id

def HomSys.comp (g : HomSys α β γ δ) (f : HomSys γ δ ε ζ) : HomSys α β ε ζ where
  toFun := f ∘ g
  edgeFun := f.edgeFun ∘ g.edgeFun

def HomSys.IsHomOn (f : HomSys α β γ δ) (G₁ : Graph α β) (G₂ : Graph γ δ) : Prop :=
  ∀ ⦃e x y⦄, G₁.Inc₂ e x y → G₂.Inc₂ (f.edgeFun e) (f x) (f y)

def HasHom (G₁ : Graph α β) (G₂ : Graph γ δ) := ∃ f : HomSys α β γ δ, f.IsHomOn G₁ G₂

def HomSys.EmbOn (f : HomSys α β γ δ) (G₁ : Graph α β) (G₂ : Graph γ δ) : Prop :=
  f.IsHomOn G₁ G₂ ∧ InjOn f G₁.V ∧ InjOn f.edgeFun G₁.E

def HasEmb (G₁ : Graph α β) (G₂ : Graph γ δ) := ∃ f : HomSys α β γ δ, f.EmbOn G₁ G₂

def HasEmb.toHasHom {G₁ : Graph α β} {G₂ : Graph γ δ} (h : HasEmb G₁ G₂) : HasHom G₁ G₂ := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, hf.1⟩

structure HomSys.IsIsomOn (f : HomSys α β γ δ) (G₁ : Graph α β) (G₂ : Graph γ δ) : Prop where
  isHomOn : f.IsHomOn G₁ G₂
  bij_vertex : BijOn f G₁.V G₂.V
  bij_edge : BijOn f.edgeFun G₁.E G₂.E

def HasIsom (G₁ : Graph α β) (G₂ : Graph γ δ) := ∃ f : HomSys α β γ δ, f.IsIsomOn G₁ G₂

lemma HasIsom.toHasEmb {G₁ : Graph α β} {G₂ : Graph γ δ} (h : HasIsom G₁ G₂) : HasEmb G₁ G₂ := by
  obtain ⟨f, hHomOn, hvinj, feinj, hvsurj, fsurj⟩ := h
  sorry
  -- exact ⟨f, ⟨hHomOn, hvinj, feinj⟩⟩

lemma  HasIsom.toHasHom {G₁ : Graph α β} {G₂ : Graph γ δ} (h : HasIsom G₁ G₂) : HasHom G₁ G₂ := by
  obtain ⟨f, hHomOn, hvinj, feinj, hvsurj, fsurj⟩ := h
  exact ⟨f, hHomOn⟩
