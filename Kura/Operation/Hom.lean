import Kura.Isolated


open Set Function
variable {α β α' β' γ δ ε ζ : Type*} {G G₁ G₁' H : Graph α β} {G₂ G₂' : Graph γ δ}
  {G₃ G₃' : Graph ε ζ} {a b c : α} {e f : β} {u v w : γ} {x y z : δ} {S S' T T' U U': Set α}
  {F F' R R' : Set β}
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

-- instance : CoeFun (HomSys α β γ δ) fun (_ : HomSys α β γ δ) ↦ β → δ where
--   coe v := v.fₑ

structure HomSys.IsHomOn (f : HomSys α β γ δ) (G₁ : Graph α β) (G₂ : Graph γ δ) : Prop where
  Mapsto_vx : MapsTo f G₁.V G₂.V
  inc₂ ⦃e x y⦄ : G₁.Inc₂ e x y → G₂.Inc₂ (f.edgeFun e) (f x) (f y)
  Mapsto_edge : MapsTo f.edgeFun G₁.E G₂.E :=
    fun _ he ↦ (inc₂ (Inc₂.exists_vx_inc₂ he).choose_spec.choose_spec).edge_mem

def HasHom (G₁ : Graph α β) (G₂ : Graph γ δ) := ∃ f : HomSys α β γ δ, f.IsHomOn G₁ G₂

scoped infix:50 " ≤⟶ " => HasHom

structure HomSys.IsEmbOn (f : HomSys α β γ δ) (G₁ : Graph α β) (G₂ : Graph γ δ) : Prop extends
  IsHomOn f G₁ G₂ where
  injOn_vx : InjOn f G₁.V
  injOn_edge : InjOn f.edgeFun G₁.E

def HasEmb (G₁ : Graph α β) (G₂ : Graph γ δ) := ∃ f : HomSys α β γ δ, f.IsEmbOn G₁ G₂

scoped infix:50 " ≤↪ " => HasEmb

def HasEmb.toHasHom {G₁ : Graph α β} {G₂ : Graph γ δ} (h : HasEmb G₁ G₂) : HasHom G₁ G₂ := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, hf.1⟩

structure HomSys.IsIsomOn (f : HomSys α β γ δ) (G₁ : Graph α β) (G₂ : Graph γ δ) : Prop extends
  IsHomOn f G₁ G₂ where
  bijOn_vx : BijOn f G₁.V G₂.V
  bijOn_edge : BijOn f.edgeFun G₁.E G₂.E

def HasIsom (G₁ : Graph α β) (G₂ : Graph γ δ) := ∃ f : HomSys α β γ δ, f.IsIsomOn G₁ G₂

scoped infix:50 " ≤↔ " => HasIsom

lemma HasIsom.toHasEmb {G₁ : Graph α β} {G₂ : Graph γ δ} (h : HasIsom G₁ G₂) : HasEmb G₁ G₂ := by
  obtain ⟨f, hHomOn, ⟨fvMps, fvInj, fvSurj⟩, feMps, heInj, feSurj⟩ := h
  use f, hHomOn

lemma  HasIsom.toHasHom {G₁ : Graph α β} {G₂ : Graph γ δ} (h : HasIsom G₁ G₂) : HasHom G₁ G₂ := by
  obtain ⟨f, hHomOn, ⟨fvMps, fvInj, fvSurj⟩, feMps, heInj, feSurj⟩ := h
  exact ⟨f, hHomOn⟩

def HomSys.id : HomSys α β α β where
  toFun := _root_.id
  edgeFun := _root_.id

lemma HomSys.IsHomOn.id : HomSys.id.IsHomOn G G where
  Mapsto_vx := fun ⦃_⦄ a ↦ a
  inc₂ := fun ⦃_ _ _⦄ a ↦ a

lemma HomSys.IsEmbOn.id : HomSys.id.IsEmbOn G G :=
  ⟨HomSys.IsHomOn.id, injOn_id G.V, injOn_id G.E⟩

lemma HomSys.IsIsomOn.id : HomSys.id.IsIsomOn G G :=
  ⟨HomSys.IsHomOn.id, bijOn_id G.V, bijOn_id G.E⟩

def HomSys.comp (g : HomSys α β γ δ) (f : HomSys γ δ ε ζ) : HomSys α β ε ζ where
  toFun := f ∘ g
  edgeFun := f.edgeFun ∘ g.edgeFun

lemma HomSys.IsHomOn.comp {g : HomSys α β γ δ} {f : HomSys γ δ ε ζ} (hg : g.IsHomOn G₁ G₂)
    (hf : f.IsHomOn G₂ G₃) : (g.comp f).IsHomOn G₁ G₃ where
  Mapsto_vx := fun ⦃_⦄ a ↦ hf.Mapsto_vx (hg.Mapsto_vx a)
  inc₂ := fun ⦃_ _ _⦄ a ↦ hf.inc₂ (hg.inc₂ a)

lemma HomSys.IsEmbOn.comp {g : HomSys α β γ δ} {f : HomSys γ δ ε ζ} (hg : g.IsEmbOn G₁ G₂)
    (hf : f.IsEmbOn G₂ G₃) : (g.comp f).IsEmbOn G₁ G₃ where
  toIsHomOn := hg.toIsHomOn.comp hf.toIsHomOn
  injOn_vx := hf.injOn_vx.comp hg.injOn_vx hg.Mapsto_vx
  injOn_edge := hf.injOn_edge.comp hg.injOn_edge hg.Mapsto_edge

lemma HomSys.IsIsomOn.comp {g : HomSys α β γ δ} {f : HomSys γ δ ε ζ} (hg : g.IsIsomOn G₁ G₂)
    (hf : f.IsIsomOn G₂ G₃) : (g.comp f).IsIsomOn G₁ G₃ where
  toIsHomOn := hg.toIsHomOn.comp hf.toIsHomOn
  bijOn_vx := hf.bijOn_vx.comp hg.bijOn_vx
  bijOn_edge := hf.bijOn_edge.comp hg.bijOn_edge

lemma HomSys.IsHomOn.le {f : HomSys α β γ δ} (hle : G₂ ≤ G₂') (hf : f.IsHomOn G₁ G₂) :
    f.IsHomOn G₁ G₂' where
  Mapsto_vx _x hx := vx_subset_of_le hle (hf.Mapsto_vx hx)
  inc₂ _e _x _y hbtw := (hf.inc₂ hbtw).le hle

lemma HomSys.IsEmbOn.le {f : HomSys α β γ δ} (hle : G₂ ≤ G₂') (hf : f.IsEmbOn G₁ G₂) :
    f.IsEmbOn G₁ G₂' where
  toIsHomOn := hf.toIsHomOn.le hle
  injOn_vx := hf.injOn_vx.mono subset_rfl
  injOn_edge := hf.injOn_edge.mono subset_rfl

lemma HasEmb.bot [hg : Nonempty γ] [hd : Nonempty δ] : (⊥ : Graph α β) ≤↪ G₂ := by
  use ⟨fun _ ↦ hg.some, fun _ ↦ hd.some⟩
  exact {
    Mapsto_vx := mapsTo_empty (fun x ↦ hg.some) G₂.V
    inc₂ := fun e x y hbtw ↦ by
      simp only [bot_E, mem_empty_iff_false, not_false_eq_true, not_inc₂_of_not_edge_mem] at hbtw
    injOn_vx := by simp only [bot_V, injOn_empty]
    injOn_edge := by simp only [bot_E, injOn_empty]
  }

section Hom

lemma HasHom.edgeless [hd : Nonempty δ] (hU : U.Nonempty) : (Edgeless U β) ≤⟶ G₂ ↔ G₂.V.Nonempty := by
  constructor
  · rintro ⟨f, hsu, hf⟩
    use f hU.some, hsu (by simp [hU.some_mem])
  · rintro ⟨v, hv⟩
    use ⟨fun _ ↦ v, fun _ ↦ hd.some⟩
    exact {
      Mapsto_vx := fun ⦃x⦄ a ↦ hv
      inc₂ := fun e x y hbtw ↦ by simp only [Edgeless.E, mem_empty_iff_false, not_false_eq_true,
        not_inc₂_of_not_edge_mem] at hbtw}

lemma HasHom.rfl : G₁ ≤⟶ G₁ := ⟨HomSys.id, HomSys.IsHomOn.id⟩

lemma HasHom.trans {G₁ : Graph α β} {G₂ : Graph γ δ} {G₃ : Graph ε ζ} (h₁₂ : G₁ ≤⟶ G₂)
    (h₂₃ : G₂ ≤⟶ G₃) : G₁ ≤⟶ G₃ := by
  obtain ⟨f₁₂, hf₁₂⟩ := h₁₂
  obtain ⟨f₂₃, hf₂₃⟩ := h₂₃
  exact ⟨f₁₂.comp f₂₃, hf₁₂.comp hf₂₃⟩

def IsCore (G : Graph α β) := ∀ f : HomSys α β α β, f.IsHomOn G G → f.IsIsomOn G G

-- lemma core_foo : ∃! H : Graph α β, H ≤ G ∧ G ≤⟶ H ∧ IsCore H := by
--   by_cases h : G.IsCore
--   · use G, ⟨le_rfl, HasHom.rfl, h⟩
--     rintro G' ⟨hG'le, ⟨f, hG'hom⟩, hG'core⟩
--     specialize h f
--   sorry

end Hom

section Emb

lemma HasEmb.rfl : G₁ ≤↪ G₁ := ⟨HomSys.id, HomSys.IsEmbOn.id⟩

lemma HasEmb.trans {G₁ : Graph α β} {G₂ : Graph γ δ} {G₃ : Graph ε ζ} (h₁₂ : G₁ ≤↪ G₂)
    (h₂₃ : G₂ ≤↪ G₃) : G₁ ≤↪ G₃ := by
  obtain ⟨f₁₂, hf₁₂⟩ := h₁₂
  obtain ⟨f₂₃, hf₂₃⟩ := h₂₃
  exact ⟨f₁₂.comp f₂₃, hf₁₂.comp hf₂₃⟩

end Emb

section Isom

lemma HasIsom.rfl : G₁ ≤↔ G₁ := ⟨HomSys.id, HomSys.IsIsomOn.id⟩

lemma HasIsom.trans {G₁ : Graph α β} {G₂ : Graph γ δ} {G₃ : Graph ε ζ} (h₁₂ : G₁ ≤↔ G₂)
    (h₂₃ : G₂ ≤↔ G₃) : G₁ ≤↔ G₃ := by
  obtain ⟨f₁₂, hf₁₂⟩ := h₁₂
  obtain ⟨f₂₃, hf₂₃⟩ := h₂₃
  exact ⟨f₁₂.comp f₂₃, hf₁₂.comp hf₂₃⟩

end Isom
