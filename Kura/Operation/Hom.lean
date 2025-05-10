import Kura.Connected
import Mathlib.Control.ULiftable


lemma Set.finite_iff_finite_of_encard_eq_encard' {α α' : Type*} {S : Set α} {T : Set α'}
    (h : S.encard = T.encard) : S.Finite ↔ T.Finite := by
  rw [← encard_lt_top_iff, ← encard_lt_top_iff, h]

lemma bijOn_encard {α α' : Type*} {f : α → α'} {S : Set α} {T : Set α'} (h : Set.BijOn f S T) :
    S.encard = T.encard := by
  rw [← h.injOn.encard_image, h.image_eq]

lemma bijOn_ncard {α α' : Type*} {f : α → α'} {S : Set α} {T : Set α'} (h : Set.BijOn f S T) :
    S.ncard = T.ncard := by
  unfold Set.ncard
  rw [← bijOn_encard h]

lemma bijOn_finite {α α' : Type*} {f : α → α'} {S : Set α} {T : Set α'} (h : Set.BijOn f S T) :
    S.Finite ↔ T.Finite := Set.finite_iff_finite_of_encard_eq_encard' (bijOn_encard h)

lemma bijOn_nonempty {α α' : Type*} {f : α → α'} {S : Set α} {T : Set α'} (h : Set.BijOn f S T) :
    S.Nonempty ↔ T.Nonempty := by
  refine ⟨fun hS ↦ ?_, fun hT ↦ ?_⟩
  · use f hS.some
    exact h.mapsTo hS.some_mem
  · obtain ⟨a, ha, heq⟩ := h.surjOn hT.some_mem
    use a

@[simp]
lemma bijOn_id {α : Type*} {S T : Set α} : Set.BijOn id S T ↔ S = T := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · ext x
    exact ⟨(h.mapsTo ·), by simpa using (h.surjOn ·)⟩
  · rintro rfl
    exact Set.bijOn_id S

open Set Function
variable {α β α' β' α'' β'' : Type*} {G G' G₁ G₁' H : Graph α β} {G₂ G₂' : Graph α' β'}
  {G₃ G₃' : Graph α'' β''} {a b c : α} {e f : β} {u v w : α'} {x y z : β''} {S S' T T' U U': Set α}
  {F F' R R' : Set β}
namespace Graph


structure HomSys (α β α' β' : Type*) where
  toFun : α → α'
  edgeFun : β → β'

@[simps]
def HomSys.ofVxFun (f : α → α') : HomSys α β α' β where
  toFun := f
  edgeFun := id

@[simps]
def HomSys.ofEdgeFun (f : β → β') : HomSys α β α β' where
  toFun := id
  edgeFun := f

instance : CoeFun (HomSys α β α' β') fun (_ : HomSys α β α' β') ↦ α → α' where
  coe v := v.toFun

-- structure HomSys.IsLawful (G : Graph α β) (f : HomSys α β α' β') : Prop where
--   forall_foo : ∀ e x y, G.Inc₂ e x y →

-- instance : CoeFun (HomSys α β α' β') fun (_ : HomSys α β α' β') ↦ β → β' where
--   coe v := v.fₑ

structure HomSys.IsHomOn (f : HomSys α β α' β') (G₁ : Graph α β) (G₂ : Graph α' β') : Prop where
  Mapsto_vx : MapsTo f G₁.V G₂.V
  inc₂ ⦃e : _⦄ ⦃x y : _⦄ : G₁.Inc₂ e x y → G₂.Inc₂ (f.edgeFun e) (f x) (f y)

  Mapsto_edge : MapsTo f.edgeFun G₁.E G₂.E :=
    fun _ he ↦ (inc₂ (exists_inc_of_mem_edgeSet he).choose_spec.choose_spec).edge_mem
  inc ⦃e : _⦄ ⦃a : _⦄ : G₁.Inc e a → G₂.Inc (f.edgeFun e) (f a) := fun hinc ↦
    (inc₂ (inc_iff_exists_inc₂.mp hinc).choose_spec).inc_left
  toMultiset ⦃e : _⦄ ⦃he : e ∈ G₁.E⦄ : (G₁.toMultiset e).map f.toFun = G₂.toMultiset (f.edgeFun e) :=
    let hbtw := exists_inc_of_mem_edgeSet he |>.choose_spec.choose_spec
    Eq.trans ((toMultiset_eq_pair_iff.mpr hbtw) ▸ rfl) (toMultiset_eq_pair_iff.mpr (inc₂ hbtw)).symm
  toSym2 ⦃e : _⦄ {he : e ∈ G₁.E} : (G₁.toSym2 e he).map f.toFun = G₂.toSym2 (f.edgeFun e) (Mapsto_edge he) :=
    let hbtw := exists_inc_of_mem_edgeSet he |>.choose_spec.choose_spec
    Eq.trans ((toSym2_eq_pair_iff he |>.mpr hbtw) ▸ rfl) (toSym2_eq_pair_iff (Mapsto_edge he) |>.mpr (inc₂ hbtw)).symm

def HomSys.IsHomOn.mk' (f : HomSys α β α' β') (hMap : MapsTo f G₁.V G₂.V)
    (hInc₂ : ∀ e x y, G₁.Inc₂ e x y → G₂.Inc₂ (f.edgeFun e) (f x) (f y)) :
    f.IsHomOn G₁ G₂ where
  Mapsto_vx := hMap
  inc₂ := hInc₂

def HasHom (G₁ : Graph α β) (G₂ : Graph α' β') := ∃ f : HomSys α β α' β', f.IsHomOn G₁ G₂

scoped infix:50 " ≤→ " => HasHom

structure HomSys.IsEmbOn (f : HomSys α β α' β') (G₁ : Graph α β) (G₂ : Graph α' β') : Prop extends
  IsHomOn f G₁ G₂ where
  injOn_vx : InjOn f G₁.V
  injOn_edge : InjOn f.edgeFun G₁.E

def HasEmb (G₁ : Graph α β) (G₂ : Graph α' β') := ∃ f : HomSys α β α' β', f.IsEmbOn G₁ G₂

scoped infix:50 " ≤↪ " => HasEmb

def HasEmb.toHasHom (h : HasEmb G₁ G₂) : HasHom G₁ G₂ := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, hf.1⟩

structure HomSys.IsIsomOn (f : HomSys α β α' β') (G₁ : Graph α β) (G₂ : Graph α' β') : Prop extends
  IsHomOn f G₁ G₂ where
  bijOn_vx : BijOn f G₁.V G₂.V
  bijOn_edge : BijOn f.edgeFun G₁.E G₂.E

lemma HomSys.IsIsomOn.toIsEmbOn (f : HomSys α β α' β') (h : f.IsIsomOn G₁ G₂) : f.IsEmbOn G₁ G₂ where
  toIsHomOn := h.toIsHomOn
  injOn_vx := h.bijOn_vx.injOn
  injOn_edge := h.bijOn_edge.injOn

lemma HomSys.IsIsomOn.ofIsEmbOn (f : HomSys α β α' β') (h : f.IsEmbOn G₁ G₂)
    (hVsurj : SurjOn f G₁.V G₂.V) (hEsurj : SurjOn f.edgeFun G₁.E G₂.E) : f.IsIsomOn G₁ G₂ where
  toIsHomOn := h.toIsHomOn
  bijOn_vx := ⟨h.Mapsto_vx, h.injOn_vx, hVsurj⟩
  bijOn_edge := ⟨h.Mapsto_edge, h.injOn_edge, hEsurj⟩

inductive HasIsom (G₁ : Graph α β) (G₂ : Graph α' β') : Prop where
  | intro (f : HomSys α β α' β') (h : f.IsIsomOn G₁ G₂)

scoped infix:50 " ≤↔ " => HasIsom

lemma HasIsom.toHasEmb (h : HasIsom G₁ G₂) : HasEmb G₁ G₂ := by
  obtain ⟨f, hHomOn, ⟨fvMps, fvInj, fvSurj⟩, feMps, heInj, feSurj⟩ := h
  use f, hHomOn

lemma HasIsom.toHasHom (h : HasIsom G₁ G₂) : HasHom G₁ G₂ := by
  obtain ⟨f, hHomOn,  ⟨fvMps, fvInj, fvSurj⟩, feMps, heInj, feSurj⟩ := h
  exact ⟨f, hHomOn⟩

@[simps]
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

@[simps]
def HomSys.comp (g : HomSys α β α' β') (f : HomSys α' β' α'' β'') : HomSys α β α'' β'' where
  toFun := f ∘ g
  edgeFun := f.edgeFun ∘ g.edgeFun

lemma HomSys.IsHomOn.comp {g : HomSys α β α' β'} {f : HomSys α' β' α'' β''} (hg : g.IsHomOn G₁ G₂)
    (hf : f.IsHomOn G₂ G₃) : (g.comp f).IsHomOn G₁ G₃ where
  Mapsto_vx := fun ⦃_⦄ a ↦ hf.Mapsto_vx (hg.Mapsto_vx a)
  inc₂ := fun ⦃_ _ _⦄ a ↦ hf.inc₂ (hg.inc₂ a)

lemma HomSys.IsEmbOn.comp {g : HomSys α β α' β'} {f : HomSys α' β' α'' β''} (hg : g.IsEmbOn G₁ G₂)
    (hf : f.IsEmbOn G₂ G₃) : (g.comp f).IsEmbOn G₁ G₃ where
  toIsHomOn := hg.toIsHomOn.comp hf.toIsHomOn
  injOn_vx := hf.injOn_vx.comp hg.injOn_vx hg.Mapsto_vx
  injOn_edge := hf.injOn_edge.comp hg.injOn_edge hg.Mapsto_edge

lemma HomSys.IsIsomOn.comp {g : HomSys α β α' β'} {f : HomSys α' β' α'' β''} (hg : g.IsIsomOn G₁ G₂)
    (hf : f.IsIsomOn G₂ G₃) : (g.comp f).IsIsomOn G₁ G₃ where
  toIsHomOn := hg.toIsHomOn.comp hf.toIsHomOn
  bijOn_vx := hf.bijOn_vx.comp hg.bijOn_vx
  bijOn_edge := hf.bijOn_edge.comp hg.bijOn_edge

lemma HomSys.IsHomOn.le {f : HomSys α β α' β'} (hle : G₂ ≤ G₂') (hf : f.IsHomOn G₁ G₂) :
    f.IsHomOn G₁ G₂' where
  Mapsto_vx _x hx := vxSet_subset_of_le hle (hf.Mapsto_vx hx)
  inc₂ _e _x _y hbtw := (hf.inc₂ hbtw).of_le hle

lemma HomSys.IsEmbOn.le {f : HomSys α β α' β'} (hle : G₂ ≤ G₂') (hf : f.IsEmbOn G₁ G₂) :
    f.IsEmbOn G₁ G₂' where
  toIsHomOn := hf.toIsHomOn.le hle
  injOn_vx := hf.injOn_vx.mono subset_rfl
  injOn_edge := hf.injOn_edge.mono subset_rfl

lemma HasEmb.bot [hg : Nonempty α'] [hd : Nonempty β'] : (⊥ : Graph α β) ≤↪ G₂ := by
  use ⟨fun _ ↦ hg.some, fun _ ↦ hd.some⟩
  exact {
    Mapsto_vx := mapsTo_empty (fun x ↦ hg.some) G₂.V
    inc₂ := fun e x y hbtw ↦ by
      simp only [bot_E, mem_empty_iff_false, not_false_eq_true, not_inc₂_of_not_mem_edgeSet] at hbtw
    injOn_vx := by simp only [bot_V, injOn_empty]
    injOn_edge := by simp only [bot_E, injOn_empty]
  }

variable {f : HomSys α β α' β'}

section Hom

lemma HasHom.noEdge [hd : Nonempty β'] (hU : U.Nonempty) :
    (Graph.noEdge U β) ≤→ G₂ ↔ G₂.V.Nonempty := by
  constructor
  · rintro ⟨f, hsu, hf⟩
    use f hU.some, hsu (by simp [hU.some_mem])
  · rintro ⟨v, hv⟩
    use ⟨fun _ ↦ v, fun _ ↦ hd.some⟩
    exact {
      Mapsto_vx := fun ⦃x⦄ a ↦ hv
      inc₂ := fun e x y hbtw ↦ by simp only [noEdge_edgeSet, mem_empty_iff_false,
        not_false_eq_true, not_inc₂_of_not_mem_edgeSet] at hbtw}

lemma HasHom.rfl : G₁ ≤→ G₁ := ⟨HomSys.id, HomSys.IsHomOn.id⟩

lemma HasHom.trans (h₁₂ : G₁ ≤→ G₂) (h₂₃ : G₂ ≤→ G₃) : G₁ ≤→ G₃ := by
  obtain ⟨f₁₂, hf₁₂⟩ := h₁₂
  obtain ⟨f₂₃, hf₂₃⟩ := h₂₃
  exact ⟨f₁₂.comp f₂₃, hf₁₂.comp hf₂₃⟩

lemma Homsys.IsHomOn.toSym2 (hisom : f.IsHomOn G₁ G₂) (he : e ∈ G₁.E):
    (G₁.toSym2 e he).map f = G₂.toSym2 (f.edgeFun e) (hisom.Mapsto_edge he) := by
  obtain ⟨a, b, hbtw⟩ := exists_inc_of_mem_edgeSet he
  rw [hbtw.toSym2, (hisom.inc₂ hbtw).toSym2]
  rfl

def IsCore (G : Graph α β) := ∀ f : HomSys α β α β, f.IsHomOn G G → f.IsIsomOn G G

-- lemma core_foo : ∃! H : Graph α β, H ≤ G ∧ G ≤→ H ∧ IsCore H := by
--   by_cases h : G.IsCore
--   · use G, ⟨le_rfl, HasHom.rfl, h⟩
--     rintro G' ⟨hG'le, ⟨f, hG'hom⟩, hG'core⟩
--     specialize h f
--   sorry

end Hom

section Emb

lemma HasEmb.rfl : G₁ ≤↪ G₁ := ⟨HomSys.id, HomSys.IsEmbOn.id⟩

lemma HasEmb.trans (h₁₂ : G₁ ≤↪ G₂) (h₂₃ : G₂ ≤↪ G₃) : G₁ ≤↪ G₃ := by
  obtain ⟨f₁₂, hf₁₂⟩ := h₁₂
  obtain ⟨f₂₃, hf₂₃⟩ := h₂₃
  exact ⟨f₁₂.comp f₂₃, hf₁₂.comp hf₂₃⟩

end Emb

section Isom

lemma HasIsom.rfl : G₁ ≤↔ G₁ := ⟨HomSys.id, HomSys.IsIsomOn.id⟩

lemma bot_hasIsom_bot [hα' : Nonempty α'] [hβ' : Nonempty β'] : (⊥ : Graph α β) ≤↔ (⊥ : Graph α' β') := by
  use ⟨fun _ ↦ hα'.some, fun _ ↦ hβ'.some⟩
  exact {
    Mapsto_vx := mapsTo_empty (fun x ↦ hα'.some) (⊥ : Graph α' β').V
    inc₂ e x y hbtw := by simp at hbtw
    bijOn_vx := by simp only [bot_V, bijOn_empty_iff_left]
    bijOn_edge := by simp only [bot_E, bijOn_empty_iff_left]}

lemma bot_hasIsom_iff [Nonempty α] [Nonempty β] : (⊥ : Graph α' β') ≤↔ G ↔ G = ⊥ := by
  constructor
  · rintro ⟨f, hf⟩
    have := hf.bijOn_vx.surjOn
    simpa using this
  · rintro rfl
    exact bot_hasIsom_bot

lemma HasIsom.symm [Nonempty α] [Nonempty β] (h : G₁ ≤↔ G₂) : G₂ ≤↔ G₁ := by
  obtain ⟨f, hHom, hBijV, hBijE⟩ := h
  have hBijVinv := (Set.bijOn_comm hBijV.invOn_invFunOn).mpr hBijV
  have hBijEinv := (Set.bijOn_comm hBijE.invOn_invFunOn).mpr hBijE
  use {toFun := invFunOn f G₁.V, edgeFun := invFunOn f.edgeFun G₁.E}, ?_, hBijVinv
  exact {
    Mapsto_vx x hx := hBijVinv.mapsTo hx
    inc₂ e x y hbtw := by
      simp only
      obtain ⟨e, he, rfl⟩ := hBijE.surjOn hbtw.edge_mem
      obtain ⟨x, hx, rfl⟩ := hBijV.surjOn hbtw.vx_mem_left
      obtain ⟨y, hy, rfl⟩ := hBijV.surjOn hbtw.vx_mem_right
      rw [hBijV.invOn_invFunOn.1 hx, hBijV.invOn_invFunOn.1 hy, hBijE.invOn_invFunOn.1 he]
      obtain ⟨u, v, huv⟩ := exists_inc₂_of_mem_edgeSet he
      have := (hHom.inc₂ huv).eq_and_eq_or_eq_and_eq_of_inc₂ hbtw
      rwa [hBijV.injOn.eq_iff huv.vx_mem_left hx, hBijV.injOn.eq_iff huv.vx_mem_left hy,
        hBijV.injOn.eq_iff huv.vx_mem_right hx, hBijV.injOn.eq_iff huv.vx_mem_right hy, ← huv.inc₂_iff] at this}

lemma HasIsom.trans (h₁₂ : G₁ ≤↔ G₂) (h₂₃ : G₂ ≤↔ G₃) : G₁ ≤↔ G₃ := by
  obtain ⟨f₁₂, hf₁₂⟩ := h₁₂
  obtain ⟨f₂₃, hf₂₃⟩ := h₂₃
  exact ⟨f₁₂.comp f₂₃, hf₁₂.comp hf₂₃⟩

lemma Homsys.IsIsomOn.inc₂_iff (hisom : f.IsIsomOn G₁ G₂) (he : e ∈ G₁.E) (ha : a ∈ G₁.V) (hb : b ∈ G₁.V) :
    G₁.Inc₂ e a b ↔ G₂.Inc₂ (f.edgeFun e) (f a) (f b) := by
  constructor <;> rintro hbtw
  · exact hisom.inc₂ hbtw
  · obtain ⟨e', he', he'eq⟩ := hisom.bijOn_edge.surjOn hbtw.edge_mem
    obtain rfl := hisom.bijOn_edge.injOn he' he he'eq
    obtain ⟨a', b', hbtw'⟩ := exists_inc_of_mem_edgeSet he
    obtain ⟨haeq, hbeq⟩ | ⟨haeq, hbeq⟩ := (hisom.inc₂ hbtw').eq_and_eq_or_eq_and_eq_of_inc₂ hbtw
    · rw [hisom.bijOn_vx.injOn.eq_iff hbtw'.vx_mem_left ha] at haeq
      rw [hisom.bijOn_vx.injOn.eq_iff hbtw'.vx_mem_right hb] at hbeq
      subst a' b'
      exact hbtw'
    · rw [hisom.bijOn_vx.injOn.eq_iff hbtw'.vx_mem_left hb] at haeq
      rw [hisom.bijOn_vx.injOn.eq_iff hbtw'.vx_mem_right ha] at hbeq
      subst a' b'
      exact hbtw'.symm

alias ⟨Inc₂.isIsomOn, _⟩ := Homsys.IsIsomOn.inc₂_iff

end Isom

def HomSys.image (f : HomSys α β α' β') (h : f.IsHomOn G G₂) : Graph α' β' :=
  ofInc (f '' G.V) (fun e' v' ↦ ∃ e, f.edgeFun e = e' ∧ ∃ v, f v = v' ∧ G.Inc e v)
  (by rintro e' v' ⟨e, rfl, v, rfl, hinc⟩; use v, hinc.vx_mem)
  (by
    rintro u' v' w' e' ⟨e, rfl, v, rfl, hincev⟩ ⟨a, heqae, b, rfl, hincab⟩ ⟨c, heqce, d, rfl, hinccd⟩
    have hev := h.inc hincev
    have hab := heqae ▸ h.inc hincab
    have hcd := heqce ▸ h.inc hinccd
    exact Inc.eq_or_eq_or_eq_of_inc_of_inc hev hab hcd)

@[simp] lemma HomSys.image_V (h : f.IsHomOn G G₂) : (f.image h).V = f '' G.V :=
  rfl

@[simp] lemma HomSys.image_E (h : f.IsHomOn G G₂) :
    (f.image h).E = f.edgeFun '' G.E := by
  ext e'
  simp only [image, ofInc_E, mem_setOf_eq, mem_image]
  constructor
  · rintro ⟨v, e, rfl, v, rfl, hinc⟩
    use e, hinc.edge_mem
  · rintro ⟨e, he, rfl⟩
    obtain ⟨v, hinc⟩ := exists_inc_of_mem_edgeSet he
    use f v, e, rfl, v

@[simp]
lemma HomSys.image_inc (h : f.IsHomOn G G₂) {e'} {v'}:
    (f.image h).Inc e' v' ↔ ∃ e, f.edgeFun e = e' ∧ ∃ v, f v = v' ∧ G.Inc e v := by
  simp only [image, ofInc_inc]

lemma HomSys.image_le (h : f.IsHomOn G G₂) : f.image h ≤ G₂ := by
  rw [le_iff_inc, image_V, image_E]
  refine ⟨image_subset_iff.mpr h.Mapsto_vx, image_subset_iff.mpr h.Mapsto_edge, ?_⟩
  rintro e he v
  simp only [image_inc]
  constructor
  · rintro ⟨e, rfl, v, rfl, hinc⟩
    exact h.inc hinc
  · rintro hinc
    obtain ⟨b, hb, rfl⟩ := he
    obtain ⟨a, a', hinc₂⟩ := exists_inc_of_mem_edgeSet hb
    obtain (rfl | rfl) := (h.inc₂ hinc₂).eq_or_eq_of_inc hinc
    · use b, rfl, a, rfl
      exact hinc₂.inc_left
    · use b, rfl, a', rfl
      exact hinc₂.inc_right

lemma HomSys.image_isIsomOn (h : f.IsEmbOn G G₂) : f.IsIsomOn G (f.image h.toIsHomOn) where
  Mapsto_vx v hv := by use v
  inc₂ e v w hbtw := by
    rw [← inc₂_iff_inc₂_of_le_of_mem (HomSys.image_le h.toIsHomOn)]
    exact h.inc₂ hbtw
    · simp only [image_E, mem_image]
      use e, hbtw.edge_mem
  bijOn_vx := ⟨fun u hu ↦ (by use u), fun u hu v hv heq ↦ h.injOn_vx hu hv heq, fun _ h ↦ h⟩
  bijOn_edge := by
    refine ⟨fun e he ↦ ?_, fun e he v hv heq ↦ h.injOn_edge he hv heq, fun d hd ↦ by
      simpa only [image_E] using hd⟩
    simp only [image_E, mem_image]
    use e

universe u₀ u₁ u₂ v₀ v₁ v₂
variable {α : Type u₀} {α' : Type u₁} {β : Type v₀} {β' : Type v₁} {χ χ' χ'' χ''' : Type*}
  [Nonempty α] [Nonempty α'] [Nonempty β] [Nonempty β'] {G : Graph α β} {G' : Graph α' β'}

class GraphicFunction (f : outParam <| ∀ {α : Type u₀} {β : Type v₀}, Graph α β → χ)
    (g : ∀ {α : Type u₁} {β : Type v₁}, Graph α β → χ) where
  invariant {α β α' β'} {G : Graph α β} {G' : Graph α' β'} : G ≤↔ G' → f G = g G'

-- class GraphicFunction  (F : ∀ {α : Type u_1} {β : Type u_2} (_G : Graph α β), χ) : Prop where
--   presv_isom {α α' β β'} [Nonempty α] [Nonempty α'] [Nonempty β] [Nonempty β']
--     (G : Graph α β) (G' : Graph α' β') : G ≤↔ G' → F G = F G'

-- variable {A B : {α : Type u₀} → {β : Type v₀} → (G : Graph α β) → χ}
--   {A' B' : {α : Type u₁} → {β : Type v₁} → (G : Graph α β) → χ'}
--   {A'' B'' : {α : Type u₂} → {β : Type v₂} → (G : Graph α β) → χ''}
--   {P P' Q Q' : {α : Type u₀} → {β : Type v₀} → (G : Graph α β) → Prop}
  -- [hA : GraphicFunction A A] [hA' : GraphicFunction A'] [hA'' : GraphicFunction A'']
  -- [hB : GraphicFunction B] [hB' : GraphicFunction B'] [hB'' : GraphicFunction B'']
  -- [hP : GraphicFunction P] [hP' : GraphicFunction P'] [hQ : GraphicFunction Q]
  -- [hQ' : GraphicFunction Q']

lemma iff_exists_isom (f : ∀ {α : Type u₀} {β : Type v₀}, Graph α β → Prop)
    (g : ∀ {α : Type (max u₀ u₁)} {β : Type (max v₀ v₁)}, Graph α β → Prop)
    [hP : GraphicFunction f g] : f G ↔ ∃ (α' : Type (max u₀ u₁)) (_ : Nonempty α')
    (β' : Type (max v₀ v₁)) (_ : Nonempty β') (G' : Graph α' β'), g G' ∧ G ≤↔ G' := by
  constructor
  · rintro h
    use ULift α, inferInstance, ULift β, inferInstance
    sorry
    -- exact ⟨h, HasIsom.rfl⟩
  · rintro ⟨α', _, β', _, G', hg, h'⟩
    rwa [hP.invariant h']

-- lemma HasIsom.eq {G G' : Graph α β} (h : G ≤↔ G') : A G = A G' := hA.presv_isom G G' h

-- lemma HasIsom.iff {G G' : Graph α β} (h : G ≤↔ G') : P G ↔ P G' := by
--   rw [← hP.presv_isom G G' h]

instance instConstGraphic (c : χ) : GraphicFunction (fun _ ↦ c) (fun _ ↦ c) where
  invariant _ := rfl

instance instCompGraphic (f : χ' → χ) : GraphicFunction (fun G ↦ f (A' G)) where
  invariant G G' h := by rw [← hA'.presv_isom G G' h]

instance instComp2Graphic (f : χ → χ' → χ'') : GraphicFunction (fun G ↦ f (A G) (A' G)) where
  presv_isom G G' h := by rw [← hA.presv_isom G G' h, ← hA'.presv_isom G G' h]

instance instComp3Graphic (f : χ → χ' → χ'' → χ''') : GraphicFunction (fun G ↦ f (A G) (A' G) (A'' G)) where
  presv_isom G G' h := by
    rw [← hA.presv_isom G G' h, ← hA'.presv_isom G G' h, ← hA''.presv_isom G G' h]

instance instImpGraphic : GraphicFunction (fun G ↦ P G → Q G) := instComp2Graphic (· → ·)

instance instHasIsomLeftGraphic : GraphicFunction (fun G ↦ G ≤↔ H) where
  presv_isom G G' h := by
    rw [eq_iff_iff]
    exact ⟨h.symm.trans, h.trans⟩

instance instHasIsomRightGraphic : GraphicFunction (fun G ↦ H ≤↔ G) where
  presv_isom G G' h := by
    rw [eq_iff_iff]
    exact ⟨(HasIsom.trans · h), (HasIsom.trans · h.symm)⟩

instance instHasEmbLeftGraphic : GraphicFunction (fun G ↦ G ≤↪ H) where
  presv_isom G G' h := by
    rw [eq_iff_iff]
    exact ⟨h.symm.toHasEmb.trans, h.toHasEmb.trans⟩

instance instHasEmbRightGraphic : GraphicFunction (fun G ↦ H ≤↪ G) where
  presv_isom G G' h := by
    rw [eq_iff_iff]
    exact ⟨(HasEmb.trans · h.toHasEmb), (HasEmb.trans · h.symm.toHasEmb)⟩

instance instHasHomLeftGraphic : GraphicFunction (fun G ↦ G ≤→ H) where
  presv_isom G G' h := by
    rw [eq_iff_iff]
    exact ⟨h.symm.toHasHom.trans, h.toHasHom.trans⟩

instance instHasHomRightGraphic : GraphicFunction (fun G ↦ H ≤→ G) where
  presv_isom G G' h := by
    rw [eq_iff_iff]
    exact ⟨(HasHom.trans · h.toHasHom), (HasHom.trans · h.symm.toHasHom)⟩

instance instVxSetFiniteGraphic : GraphicFunction (fun G ↦ Finite G.V) where
  presv_isom G G' h := by
    rw [eq_iff_iff]
    obtain ⟨f, hf⟩ := h
    exact bijOn_finite hf.bijOn_vx

instance instEdgeSetFiniteGraphic : GraphicFunction (fun G ↦ Finite G.E) where
  presv_isom G G' h := by
    rw [eq_iff_iff]
    obtain ⟨f, hf⟩ := h
    exact bijOn_finite hf.bijOn_edge

instance instVxSetNonemptyGraphic : GraphicFunction (fun G ↦ G.V.Nonempty) where
  presv_isom G G' h := by
    rw [eq_iff_iff]
    obtain ⟨f, hf⟩ := h
    exact bijOn_nonempty hf.bijOn_vx

instance instEdgeSetNonemptyGraphic : GraphicFunction (fun G ↦ G.E.Nonempty) where
  presv_isom G G' h := by
    rw [eq_iff_iff]
    obtain ⟨f, hf⟩ := h
    exact bijOn_nonempty hf.bijOn_edge

instance instVxSetEncardGraphic : GraphicFunction (fun G ↦ G.V.encard) where
  presv_isom G G' h := by
    obtain ⟨f, hf⟩ := h
    exact bijOn_encard hf.bijOn_vx

instance instEdgeSetEncardGraphic : GraphicFunction (fun G ↦ G.E.encard) where
  presv_isom G G' h := by
    obtain ⟨f, hf⟩ := h
    exact bijOn_encard hf.bijOn_edge

instance instVxSetNcardGraphic : GraphicFunction (fun G ↦ G.V.ncard) where
  presv_isom G G' h := by
    obtain ⟨f, hf⟩ := h
    exact bijOn_ncard hf.bijOn_vx

instance instEdgeSetNcardGraphic : GraphicFunction (fun G ↦ G.E.ncard) where
  presv_isom G G' h := by
    obtain ⟨f, hf⟩ := h
    exact bijOn_ncard hf.bijOn_edge


class GraphicVertexFunction {χ : Type*} (F : ∀ {β : Type u_2}, Graph α β → χ) : Prop where
  presv_isom {β β' : Type u_2} [Nonempty β] [Nonempty β']
    (G : Graph α β) (G' : Graph α β') (h : ∃ f : β → β', (HomSys.ofEdgeFun f).IsIsomOn G G') : F G = F G'

-- WHY IS THIS NOT WORKING?
instance instGraphicGraphicVertex {F : {α : Type u_1} → {β : Type u_2} → Graph α β → χ}
    [hF : GraphicFunction F] : GraphicVertexFunction (fun G ↦ F (α := α) G) where
  presv_isom G G' h := by
    obtain ⟨f, hf⟩ := h
    rw [← hF.presv_isom G G' ⟨HomSys.ofEdgeFun f, hf⟩]

variable {A B : {β : Type u_2} → (G : Graph α β) → χ}
  {A' B' : {β : Type u_2} → (G : Graph α β) → χ'}
  {A'' B'' : {β : Type u_2} → (G : Graph α β) → χ''}
  {P P' Q Q' : {β : Type u_2} → (G : Graph α β) → Prop}
  [hA : GraphicVertexFunction A] [hA' : GraphicVertexFunction A'] [hA'' : GraphicVertexFunction A'']
  [hB : GraphicVertexFunction B] [hB' : GraphicVertexFunction B'] [hB'' : GraphicVertexFunction B'']
  [hP : GraphicVertexFunction P] [hP' : GraphicVertexFunction P'] [hQ : GraphicVertexFunction Q]
  [hQ' : GraphicVertexFunction Q']

instance instConstGraphicVertex (c : χ) : GraphicVertexFunction (fun (_ : Graph α _) ↦ c) where
  presv_isom _ _ _ := rfl

instance instCompGraphicVertex (f : χ' → χ) : GraphicVertexFunction (fun G ↦ f (A' G)) where
  presv_isom G G' h := by rw [← hA'.presv_isom G G' h]

instance instComp2GraphicVertex (f : χ → χ' → χ'') : GraphicVertexFunction (fun G ↦ f (A G) (A' G)) where
  presv_isom G G' h := by rw [← hA.presv_isom G G' h, ← hA'.presv_isom G G' h]

instance instComp3GraphicVertex (f : χ → χ' → χ'' → χ''') : GraphicVertexFunction (fun G ↦ f (A G) (A' G) (A'' G)) where
  presv_isom G G' h := by
    rw [← hA.presv_isom G G' h, ← hA'.presv_isom G G' h, ← hA''.presv_isom G G' h]

instance instImpGraphicVertex : GraphicVertexFunction (fun G ↦ P G → Q G) :=
  instComp2GraphicVertex (· → ·)

instance instHasIsomLeftGraphicVertex : GraphicVertexFunction (fun (G : Graph α _) ↦ G ≤↔ H) :=
  instGraphicGraphicVertex (hF := instHasIsomLeftGraphic)

instance instHasIsomRightGraphicVertex : GraphicVertexFunction (fun (G : Graph α _) ↦ H ≤↔ G) :=
  instGraphicGraphicVertex (hF := instHasIsomRightGraphic)

instance instHasEmbLeftGraphicVertex : GraphicVertexFunction (fun (G : Graph α _) ↦ G ≤↪ H) :=
  instGraphicGraphicVertex (hF := instHasEmbLeftGraphic)

instance instHasEmbRightGraphicVertex : GraphicVertexFunction (fun (G : Graph α _) ↦ H ≤↪ G) :=
  instGraphicGraphicVertex (hF := instHasEmbRightGraphic)

instance instHasHomLeftGraphicVertex : GraphicVertexFunction (fun (G : Graph α _) ↦ G ≤→ H) :=
  instGraphicGraphicVertex (hF := instHasHomLeftGraphic)

instance instHasHomRightGraphicVertex : GraphicVertexFunction (fun (G : Graph α _) ↦ H ≤→ G) :=
  instGraphicGraphicVertex (hF := instHasHomRightGraphic)

instance instVxSetGraphicVertex : GraphicVertexFunction (fun {β : Type u_2} (G : Graph α β) ↦ G.V) where
  presv_isom G G' h := by
    obtain ⟨f, hf⟩ := h
    simpa only [HomSys.ofEdgeFun, _root_.bijOn_id] using hf.bijOn_vx

instance instEdgeSetFiniteGraphicVertex : GraphicVertexFunction (fun {β : Type u_2} (G : Graph α β) ↦ Finite G.E) :=
  instGraphicGraphicVertex (hF := instEdgeSetFiniteGraphic)

instance instEdgeSetNonemptyGraphicVertex : GraphicVertexFunction (fun {β : Type u_2} (G : Graph α β) ↦ G.E.Nonempty) :=
  instGraphicGraphicVertex (hF := instEdgeSetNonemptyGraphic)

instance instEdgeSetEncardGraphicVertex : GraphicVertexFunction (fun {β : Type u_2} (G : Graph α β) ↦ G.E.encard) :=
  instGraphicGraphicVertex (hF := instEdgeSetEncardGraphic)

instance instEdgeSetNcardGraphicVertex : GraphicVertexFunction (fun {β : Type u_2} (G : Graph α β) ↦ G.E.ncard) :=
  instGraphicGraphicVertex (hF := instEdgeSetNcardGraphic)
