import Kura.Connected


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

open Set Function
variable {α ε α' ε' α'' ε'' : Type*} {G G' G₁ G₁' H : Graph α ε} {G₂ G₂' : Graph α' ε'}
  {G₃ G₃' : Graph α'' ε''} {a b c : α} {e f : ε} {u v w : α'} {x y z : ε''} {S S' T T' U U': Set α}
  {F F' R R' : Set ε}
namespace Graph


structure HomSys (α ε α' ε' : Type*) where
  toFun : α → α'
  edgeFun : ε → ε'

@[simps]
def HomSys.ofVxFun (f : α → α') : HomSys α ε α' ε where
  toFun := f
  edgeFun := id

instance : CoeFun (HomSys α ε α' ε') fun (_ : HomSys α ε α' ε') ↦ α → α' where
  coe v := v.toFun

-- structure HomSys.IsLawful (G : Graph α ε) (f : HomSys α ε α' ε') : Prop where
--   forall_foo : ∀ e x y, G.Inc₂ e x y →

-- instance : CoeFun (HomSys α ε α' ε') fun (_ : HomSys α ε α' ε') ↦ ε → ε' where
--   coe v := v.fₑ

structure HomSys.IsHomOn (f : HomSys α ε α' ε') (G₁ : Graph α ε) (G₂ : Graph α' ε') : Prop where
  Mapsto_vx : MapsTo f G₁.V G₂.V
  inc₂ ⦃e : _⦄ ⦃x y : _⦄ : G₁.Inc₂ e x y → G₂.Inc₂ (f.edgeFun e) (f x) (f y)

  Mapsto_edge : MapsTo f.edgeFun G₁.E G₂.E :=
    fun _ he ↦ (inc₂ (exists_inc_of_mem_edgeSet he).choose_spec.choose_spec).edge_mem
  inc ⦃e : _⦄ ⦃a : _⦄ : G₁.Inc e a → G₂.Inc (f.edgeFun e) (f a) := fun hinc ↦
    (inc₂ (inc_iff_exists_inc₂.mp hinc).choose_spec).inc_left

def HomSys.IsHomOn.mk' (f : HomSys α ε α' ε') (hMap : MapsTo f G₁.V G₂.V)
    (hInc₂ : ∀ e x y, G₁.Inc₂ e x y → G₂.Inc₂ (f.edgeFun e) (f x) (f y)) :
    f.IsHomOn G₁ G₂ where
  Mapsto_vx := hMap
  inc₂ := hInc₂

def HasHom (G₁ : Graph α ε) (G₂ : Graph α' ε') := ∃ f : HomSys α ε α' ε', f.IsHomOn G₁ G₂

scoped infix:50 " ≤→ " => HasHom

structure HomSys.IsEmbOn (f : HomSys α ε α' ε') (G₁ : Graph α ε) (G₂ : Graph α' ε') : Prop extends
  IsHomOn f G₁ G₂ where
  injOn_vx : InjOn f G₁.V
  injOn_edge : InjOn f.edgeFun G₁.E

def HasEmb (G₁ : Graph α ε) (G₂ : Graph α' ε') := ∃ f : HomSys α ε α' ε', f.IsEmbOn G₁ G₂

scoped infix:50 " ≤↪ " => HasEmb

def HasEmb.toHasHom (h : HasEmb G₁ G₂) : HasHom G₁ G₂ := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, hf.1⟩

structure HomSys.IsIsomOn (f : HomSys α ε α' ε') (G₁ : Graph α ε) (G₂ : Graph α' ε') : Prop extends
  IsHomOn f G₁ G₂ where
  bijOn_vx : BijOn f G₁.V G₂.V
  bijOn_edge : BijOn f.edgeFun G₁.E G₂.E

lemma HomSys.IsIsomOn.toIsEmbOn (f : HomSys α ε α' ε') (h : f.IsIsomOn G₁ G₂) : f.IsEmbOn G₁ G₂ where
  toIsHomOn := h.toIsHomOn
  injOn_vx := h.bijOn_vx.injOn
  injOn_edge := h.bijOn_edge.injOn

lemma HomSys.IsIsomOn.ofIsEmbOn (f : HomSys α ε α' ε') (h : f.IsEmbOn G₁ G₂)
    (hVsurj : SurjOn f G₁.V G₂.V) (hEsurj : SurjOn f.edgeFun G₁.E G₂.E) : f.IsIsomOn G₁ G₂ where
  toIsHomOn := h.toIsHomOn
  bijOn_vx := ⟨h.Mapsto_vx, h.injOn_vx, hVsurj⟩
  bijOn_edge := ⟨h.Mapsto_edge, h.injOn_edge, hEsurj⟩

inductive HasIsom (G₁ : Graph α ε) (G₂ : Graph α' ε') : Prop where
  | intro (f : HomSys α ε α' ε') (h : f.IsIsomOn G₁ G₂)

scoped infix:50 " ≤↔ " => HasIsom

lemma HasIsom.toHasEmb (h : HasIsom G₁ G₂) : HasEmb G₁ G₂ := by
  obtain ⟨f, hHomOn, ⟨fvMps, fvInj, fvSurj⟩, feMps, heInj, feSurj⟩ := h
  use f, hHomOn

lemma HasIsom.toHasHom (h : HasIsom G₁ G₂) : HasHom G₁ G₂ := by
  obtain ⟨f, hHomOn,  ⟨fvMps, fvInj, fvSurj⟩, feMps, heInj, feSurj⟩ := h
  exact ⟨f, hHomOn⟩

@[simps]
def HomSys.id : HomSys α ε α ε where
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
def HomSys.comp (g : HomSys α ε α' ε') (f : HomSys α' ε' α'' ε'') : HomSys α ε α'' ε'' where
  toFun := f ∘ g
  edgeFun := f.edgeFun ∘ g.edgeFun

lemma HomSys.IsHomOn.comp {g : HomSys α ε α' ε'} {f : HomSys α' ε' α'' ε''} (hg : g.IsHomOn G₁ G₂)
    (hf : f.IsHomOn G₂ G₃) : (g.comp f).IsHomOn G₁ G₃ where
  Mapsto_vx := fun ⦃_⦄ a ↦ hf.Mapsto_vx (hg.Mapsto_vx a)
  inc₂ := fun ⦃_ _ _⦄ a ↦ hf.inc₂ (hg.inc₂ a)

lemma HomSys.IsEmbOn.comp {g : HomSys α ε α' ε'} {f : HomSys α' ε' α'' ε''} (hg : g.IsEmbOn G₁ G₂)
    (hf : f.IsEmbOn G₂ G₃) : (g.comp f).IsEmbOn G₁ G₃ where
  toIsHomOn := hg.toIsHomOn.comp hf.toIsHomOn
  injOn_vx := hf.injOn_vx.comp hg.injOn_vx hg.Mapsto_vx
  injOn_edge := hf.injOn_edge.comp hg.injOn_edge hg.Mapsto_edge

lemma HomSys.IsIsomOn.comp {g : HomSys α ε α' ε'} {f : HomSys α' ε' α'' ε''} (hg : g.IsIsomOn G₁ G₂)
    (hf : f.IsIsomOn G₂ G₃) : (g.comp f).IsIsomOn G₁ G₃ where
  toIsHomOn := hg.toIsHomOn.comp hf.toIsHomOn
  bijOn_vx := hf.bijOn_vx.comp hg.bijOn_vx
  bijOn_edge := hf.bijOn_edge.comp hg.bijOn_edge

lemma HomSys.IsHomOn.le {f : HomSys α ε α' ε'} (hle : G₂ ≤ G₂') (hf : f.IsHomOn G₁ G₂) :
    f.IsHomOn G₁ G₂' where
  Mapsto_vx _x hx := vxSet_subset_of_le hle (hf.Mapsto_vx hx)
  inc₂ _e _x _y hbtw := (hf.inc₂ hbtw).of_le hle

lemma HomSys.IsEmbOn.le {f : HomSys α ε α' ε'} (hle : G₂ ≤ G₂') (hf : f.IsEmbOn G₁ G₂) :
    f.IsEmbOn G₁ G₂' where
  toIsHomOn := hf.toIsHomOn.le hle
  injOn_vx := hf.injOn_vx.mono subset_rfl
  injOn_edge := hf.injOn_edge.mono subset_rfl

lemma HasEmb.bot [hg : Nonempty α'] [hd : Nonempty ε'] : (⊥ : Graph α ε) ≤↪ G₂ := by
  use ⟨fun _ ↦ hg.some, fun _ ↦ hd.some⟩
  exact {
    Mapsto_vx := mapsTo_empty (fun x ↦ hg.some) G₂.V
    inc₂ := fun e x y hbtw ↦ by
      simp only [bot_E, mem_empty_iff_false, not_false_eq_true, not_inc₂_of_not_mem_edgeSet] at hbtw
    injOn_vx := by simp only [bot_V, injOn_empty]
    injOn_edge := by simp only [bot_E, injOn_empty]
  }

variable {f : HomSys α ε α' ε'}

section Hom

lemma HasHom.noEdge [hd : Nonempty ε'] (hU : U.Nonempty) :
    (Graph.noEdge U ε) ≤→ G₂ ↔ G₂.V.Nonempty := by
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

def IsCore (G : Graph α ε) := ∀ f : HomSys α ε α ε, f.IsHomOn G G → f.IsIsomOn G G

-- lemma core_foo : ∃! H : Graph α ε, H ≤ G ∧ G ≤→ H ∧ IsCore H := by
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

lemma bot_hasIsom_bot [hα' : Nonempty α'] [hε' : Nonempty ε'] : (⊥ : Graph α ε) ≤↔ (⊥ : Graph α' ε') := by
  use ⟨fun _ ↦ hα'.some, fun _ ↦ hε'.some⟩
  exact {
    Mapsto_vx := mapsTo_empty (fun x ↦ hα'.some) (⊥ : Graph α' ε').V
    inc₂ e x y hbtw := by simp at hbtw
    bijOn_vx := by simp only [bot_V, bijOn_empty_iff_left]
    bijOn_edge := by simp only [bot_E, bijOn_empty_iff_left]}

lemma bot_hasIsom_iff [Nonempty α] [Nonempty ε] : (⊥ : Graph α' ε') ≤↔ G ↔ G = ⊥ := by
  constructor
  · rintro ⟨f, hf⟩
    have := hf.bijOn_vx.surjOn
    simpa using this
  · rintro rfl
    exact bot_hasIsom_bot

lemma HasIsom.symm [Nonempty α] [Nonempty ε] (h : G₁ ≤↔ G₂) : G₂ ≤↔ G₁ := by
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

lemma IsIsomOn.inc₂ (hisom : f.IsIsomOn G₁ G₂) (he : e ∈ G₁.E) (ha : a ∈ G₁.V) (hb : b ∈ G₁.V) :
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

alias ⟨Inc₂.isIsomOn, _⟩ := IsIsomOn.inc₂

end Isom

def HomSys.image (f : HomSys α ε α' ε') (h : f.IsHomOn G G₂) : Graph α' ε' :=
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

variable {α' : Type u_1} {ε' : Type u_2} {χ χ' χ'' χ''' : Type*} [Nonempty α] [Nonempty α']
  [Nonempty ε] [Nonempty ε'] {G' : Graph α' ε'}

class GraphicFunction  (F : {α : Type u_1} → {ε : Type u_2} → (G : Graph α ε) → χ) : Prop where
  presv_isom {α α' : Type u_1} {ε ε' : Type u_2} [Nonempty α] [Nonempty α'] [Nonempty ε] [Nonempty ε']
    (G : Graph α ε) (G' : Graph α' ε') : G ≤↔ G' → F G = F G'

variable {A B : {α : Type u_1} → {ε : Type u_2} → (G : Graph α ε) → χ}
  {A' B' : {α : Type u_1} → {ε : Type u_2} → (G : Graph α ε) → χ'}
  {A'' B'' : {α : Type u_1} → {ε : Type u_2} → (G : Graph α ε) → χ''}
  {P P' Q Q' : {α : Type u_1} → {ε : Type u_2} → (G : Graph α ε) → Prop}
  [hA : GraphicFunction A] [hA' : GraphicFunction A'] [hA'' : GraphicFunction A'']
  [hB : GraphicFunction B] [hB' : GraphicFunction B'] [hB'' : GraphicFunction B'']
  [hP : GraphicFunction P] [hP' : GraphicFunction P'] [hQ : GraphicFunction Q]
  [hQ' : GraphicFunction Q']

lemma iff_exists_isom (P : {α : Type u_1} → {ε : Type u_2} → (G : Graph α ε) → Prop)
    [hP : GraphicFunction P] : P G ↔
    ∃ (α' : Type _) (_ : Nonempty α') (ε' : Type _) (_ : Nonempty ε') (G' : Graph α' ε'),
      P G' ∧ G ≤↔ G' := by
  constructor
  · rintro h
    use α, inferInstance, ε, inferInstance, G
    exact ⟨h, HasIsom.rfl⟩
  · rintro ⟨α', _, ε', _, G', h, h'⟩
    rwa [hP.presv_isom G G' h']

lemma HasIsom.eq {G G' : Graph α ε} (h : G ≤↔ G') : A G = A G' := hA.presv_isom G G' h

lemma HasIsom.iff {G G' : Graph α ε} (h : G ≤↔ G') : P G ↔ P G' := by
  rw [← hP.presv_isom G G' h]

instance instConstGraphic (c : χ) : GraphicFunction (fun _ ↦ c) where
  presv_isom _ _ _ := rfl

instance instCompGraphic (f : χ' → χ) : GraphicFunction (fun G ↦ f (A' G)) where
  presv_isom G G' h := by rw [← hA'.presv_isom G G' h]

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
