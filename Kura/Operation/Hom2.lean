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

@[simp]
lemma bijOn_id {α : Type*} {S T : Set α} : Set.BijOn id S T ↔ S = T := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · ext x
    exact ⟨(h.mapsTo ·), by simpa using (h.surjOn ·)⟩
  · rintro rfl
    exact Set.bijOn_id S

open Set Function
variable {α ε α' ε' α'' ε'' : Type*} {G G₁ H : Graph α ε} {G' H' : Graph α' ε'}
  {G'' H'' : Graph α'' ε''} {a b c : α} {e f : ε} {u v w : α'} {x y z : ε''} {S S' T T' U U': Set α}
  {F F' R R' : Set ε}
namespace Graph


structure Funs (G : Graph α ε) (G' : Graph α' ε') where
  toFun : G.V → G'.V
  edgeFun : G.E → G'.E

instance : CoeFun (Funs G G') fun (_ : Funs G G') ↦ G.V → G'.V where
  coe v := v.toFun

@[simps]
def Funs.ofVxFun {G' : Graph α' ε} (f : G.V → G'.V) (hE : G.E = G'.E) : Funs G G' where
  toFun := f
  edgeFun := fun ⟨e, he⟩ ↦ ⟨e, hE ▸ he⟩

@[simps]
def Funs.ofEdgeFun {G' : Graph α ε'} (f : G.E → G'.E) (hV : G.V = G'.V) : Funs G G' where
  toFun := fun ⟨v, hv⟩ ↦ ⟨v, hV ▸ hv⟩
  edgeFun := f

@[simps]
def Funs.id : Funs G G where
  toFun := _root_.id
  edgeFun := _root_.id

@[simps]
def Funs.comp {G' : Graph α' ε'} {G'' : Graph α'' ε''} (f : Funs G G') (g : Funs G' G'') : Funs G G'' where
  toFun := g.toFun ∘ f.toFun
  edgeFun := g.edgeFun ∘ f.edgeFun

lemma exists_funs (hV : G'.V.Nonempty) (hE : G'.E.Nonempty) : ∃ _ : Funs G G', True := by
  use {
    toFun := fun _ ↦ ⟨hV.some, hV.some_mem⟩
    edgeFun := fun _ ↦ ⟨hE.some, hE.some_mem⟩
  }


structure Hom (G : Graph α ε) (G' : Graph α' ε') extends Funs G G' where
  inc₂ ⦃e : G.E⦄ ⦃x y : G.V⦄ : G.Inc₂ e x y → G'.Inc₂ (edgeFun e) (toFun x) (toFun y)

  -- inc ⦃e : G.E⦄ ⦃a : G.V⦄ : G.Inc e a → G'.Inc (edgeFun e) (toFun a) := fun hinc ↦
  --   (inc₂ (inc_iff_exists_inc₂.mp hinc).choose_spec).inc_left
  -- toMultiset ⦃e : G.E⦄ : (G.toMultiset e).map toFun = G'.toMultiset (edgeFun e) := by
  --   obtain ⟨a, b, hbtw⟩ := exists_inc_of_mem_edgeSet he
  --   rw [toMultiset_eq_pair_iff.mpr hbtw, toMultiset_eq_pair_iff.mpr (f.inc₂ hbtw)]
  --   rfl
  func ⦃e : _⦄ : (G.func e).map toFun = G'.func (edgeFun e) :=
    let h := exists_func_pair e |>.choose_spec.choose_spec
    ((congrArg _ h).trans (Sym2.map_pair_eq toFun _ _)).trans (func_eq_pair_iff.mpr (inc₂ <| func_eq_pair_iff.mp h)).symm

@[simps!]
def Hom.id : Hom G G where
  toFuns := Funs.id
  inc₂ _ _ _ hbtw := hbtw

@[simps!]
def Hom.comp {G' : Graph α' ε'} (f : Hom G G') (g : Hom G' G'') : Hom G G'' where
  toFuns := Funs.comp f.toFuns g.toFuns
  inc₂ _ _ _ hbtw := g.inc₂ (f.inc₂ hbtw)

inductive HasHom (G₁ : Graph α ε) (G₂ : Graph α' ε') : Prop where
  | intro (f : Hom G₁ G₂)

scoped infix:50 " →ᴳ " => HasHom

lemma HasHom.rfl : G →ᴳ G := ⟨Hom.id⟩

lemma HasHom.trans (h₁₂ : G →ᴳ G') (h₂₃ : G' →ᴳ G'') : G →ᴳ G'' := by
  obtain ⟨f⟩ := h₁₂
  obtain ⟨g⟩ := h₂₃
  exact ⟨f.comp g⟩

-- Todo: Add some stuff about cardinality

structure Emb (G₁ : Graph α ε) (G₂ : Graph α' ε') extends Hom G₁ G₂ where
  inj_vx : Injective toFun
  inj_edge : Injective edgeFun

@[simps!]
def Emb.id : Emb G G where
  toHom := Hom.id
  inj_vx ⦃_ _⦄ h := h
  inj_edge ⦃_ _⦄ h := h

@[simps!]
def Emb.comp {G' : Graph α' ε'} (f : Emb G G') (g : Emb G' G'') : Emb G G'' where
  toHom := Hom.comp f.toHom g.toHom
  inj_vx ⦃_ _⦄ h := f.inj_vx (g.inj_vx h)
  inj_edge ⦃_ _⦄ h := f.inj_edge (g.inj_edge h)

inductive HasEmb (G₁ : Graph α ε) (G₂ : Graph α' ε') : Prop where
  | intro (f : Emb G₁ G₂)

scoped infix:50 " ↪ᴳ " => HasEmb

def HasEmb.toHasHom (h : HasEmb G G') : HasHom G G' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f⟩

lemma HasEmb.rfl : G ↪ᴳ G := ⟨Emb.id⟩

lemma HasEmb.trans (h₁₂ : G ↪ᴳ G') (h₂₃ : G' ↪ᴳ G'') : G ↪ᴳ G'' := by
  obtain ⟨f⟩ := h₁₂
  obtain ⟨g⟩ := h₂₃
  exact ⟨f.comp g⟩

lemma HasEmb.of_le (hle : G ≤ G₁) : G ↪ᴳ G₁ := by
  exact ⟨{
    toFun v := ⟨v, vxSet_subset_of_le hle v.prop⟩
    edgeFun e := ⟨e, edgeSet_subset_of_le hle e.prop⟩
    inc₂ e x y hbtw := hbtw.of_le hle
    inj_vx x y h := by
      simp only [Subtype.mk.injEq] at h
      exact SetCoe.ext h
    inj_edge e f h := by
      simp only [Subtype.mk.injEq] at h
      exact SetCoe.ext h
  }⟩

lemma HasEmb.bot : (⊥ : Graph α ε) ↪ᴳ (⊥ : Graph α' ε') := ⟨{
    toFun v := IsEmpty.elim (α := (∅ : Set α).Elem) inferInstance v
    edgeFun e := IsEmpty.elim (α := (∅ : Set ε).Elem) inferInstance e
    inc₂ e := IsEmpty.elim (α := (∅ : Set ε).Elem) inferInstance e
    inj_vx v := IsEmpty.elim (α := (∅ : Set α).Elem) inferInstance v
    inj_edge e := IsEmpty.elim (α := (∅ : Set ε).Elem) inferInstance e
  }⟩


structure Isom (G₁ : Graph α ε) (G₂ : Graph α' ε') extends Hom G₁ G₂ where
  invFun : G₂.V → G₁.V
  vx_right_inv : RightInverse toFun invFun
  vx_left_inv : LeftInverse toFun invFun
  edgeInvFun : G₂.E → G₁.E
  edge_right_inv : RightInverse edgeFun edgeInvFun
  edge_left_inv : LeftInverse edgeFun edgeInvFun

def Isom.toEmb (f : Isom G G') : Emb G G' where
  toHom := f.toHom
  inj_vx := f.vx_right_inv.injective
  inj_edge := f.edge_right_inv.injective

-- ToDo: Isom.ofEmb
-- ToDo: Isom.ofEquiv

@[simps!]
def Isom.id : Isom G G where
  toHom := Hom.id
  invFun := _root_.id
  vx_right_inv := congrFun rfl
  vx_left_inv := congrFun rfl
  edgeInvFun := _root_.id
  edge_right_inv := congrFun rfl
  edge_left_inv := congrFun rfl

@[simps!]
def Isom.comp {G' : Graph α' ε'} (f : Isom G G') (g : Isom G' G'') : Isom G G'' where
  toHom := Hom.comp f.toHom g.toHom
  invFun := f.invFun ∘ g.invFun
  vx_right_inv x := by
    simp only [Hom.comp_toFun, comp_apply, g.vx_right_inv (f.toFun x), f.vx_right_inv x]
  vx_left_inv x := by
    simp only [Hom.comp_toFun, comp_apply, g.vx_left_inv x, f.vx_left_inv (g.invFun x)]
  edgeInvFun := f.edgeInvFun ∘ g.edgeInvFun
  edge_right_inv e := by
    simp only [Hom.comp_edgeFun, comp_apply, g.edge_right_inv (f.edgeFun e), f.edge_right_inv e]
  edge_left_inv e := by
    simp only [Hom.comp_edgeFun, comp_apply, g.edge_left_inv e, f.edge_left_inv (g.edgeInvFun e)]

inductive HasIsom (G₁ : Graph α ε) (G₂ : Graph α' ε') : Prop where
  | intro (f : Isom G₁ G₂)

scoped infix:50 " ↔ᴳ " => HasIsom

lemma HasIsom.toHasEmb (h : HasIsom G G') : HasEmb G G' := by
  obtain ⟨f⟩ := h
  exact ⟨f.toEmb⟩

lemma HasIsom.toHasHom (h : HasIsom G G') : HasHom G G' := by
  obtain ⟨f⟩ := h
  exact ⟨f.toHom⟩

lemma HasIsom.rfl : G ↔ᴳ G := ⟨Isom.id⟩

lemma HasIsom.trans (h₁₂ : G ↔ᴳ G') (h₂₃ : G' ↔ᴳ G'') : G ↔ᴳ G'' := by
  obtain ⟨f⟩ := h₁₂
  obtain ⟨g⟩ := h₂₃
  exact ⟨f.comp g⟩

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

lemma Homsys.IsHomOn.toSym2 (hisom : f.IsHomOn G₁ G₂) (he : e ∈ G₁.E):
    (G₁.toSym2 e he).map f = G₂.toSym2 (f.edgeFun e) (hisom.Mapsto_edge he) := by
  obtain ⟨a, b, hbtw⟩ := exists_inc_of_mem_edgeSet he
  rw [hbtw.toSym2, (hisom.inc₂ hbtw).toSym2]
  rfl

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

class GraphicFunction  (F : ∀ {α : Type u_1} {ε : Type u_2} (_G : Graph α ε), χ) : Prop where
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


class GraphicVertexFunction {χ : Type*} (F : ∀ {ε : Type u_2}, Graph α ε → χ) : Prop where
  presv_isom {ε ε' : Type u_2} [Nonempty ε] [Nonempty ε']
    (G : Graph α ε) (G' : Graph α ε') (h : ∃ f : ε → ε', (HomSys.ofEdgeFun f).IsIsomOn G G') : F G = F G'

-- WHY IS THIS NOT WORKING?
instance instGraphicGraphicVertex {F : {α : Type u_1} → {ε : Type u_2} → Graph α ε → χ}
    [hF : GraphicFunction F] : GraphicVertexFunction (fun G ↦ F (α := α) G) where
  presv_isom G G' h := by
    obtain ⟨f, hf⟩ := h
    rw [← hF.presv_isom G G' ⟨HomSys.ofEdgeFun f, hf⟩]

variable {A B : {ε : Type u_2} → (G : Graph α ε) → χ}
  {A' B' : {ε : Type u_2} → (G : Graph α ε) → χ'}
  {A'' B'' : {ε : Type u_2} → (G : Graph α ε) → χ''}
  {P P' Q Q' : {ε : Type u_2} → (G : Graph α ε) → Prop}
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

instance instVxSetGraphicVertex : GraphicVertexFunction (fun {ε : Type u_2} (G : Graph α ε) ↦ G.V) where
  presv_isom G G' h := by
    obtain ⟨f, hf⟩ := h
    simpa only [HomSys.ofEdgeFun, _root_.bijOn_id] using hf.bijOn_vx

instance instEdgeSetFiniteGraphicVertex : GraphicVertexFunction (fun {ε : Type u_2} (G : Graph α ε) ↦ Finite G.E) :=
  instGraphicGraphicVertex (hF := instEdgeSetFiniteGraphic)

instance instEdgeSetNonemptyGraphicVertex : GraphicVertexFunction (fun {ε : Type u_2} (G : Graph α ε) ↦ G.E.Nonempty) :=
  instGraphicGraphicVertex (hF := instEdgeSetNonemptyGraphic)

instance instEdgeSetEncardGraphicVertex : GraphicVertexFunction (fun {ε : Type u_2} (G : Graph α ε) ↦ G.E.encard) :=
  instGraphicGraphicVertex (hF := instEdgeSetEncardGraphic)

instance instEdgeSetNcardGraphicVertex : GraphicVertexFunction (fun {ε : Type u_2} (G : Graph α ε) ↦ G.E.ncard) :=
  instGraphicGraphicVertex (hF := instEdgeSetNcardGraphic)
