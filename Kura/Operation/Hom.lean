import Kura.Operation.Map


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

lemma Function.Bijective.nonempty_iff {α α' : Type*} {f : α → α'} (hf : Bijective f) :
    Nonempty α ↔ Nonempty α' :=
  ⟨Nonempty.map f, Nonempty.map (Equiv.ofBijective f hf).invFun⟩

@[simp]
lemma nonempty_equiv_empty {α β : Type*} : Nonempty ((∅ : Set α) ≃ (∅ : Set β)) :=
  ⟨Equiv.equivOfIsEmpty _ _⟩


open Set Function
variable {α β α' β' α'' β'' : Type*} {G G₁ H : Graph α β} {G' H' : Graph α' β'}
  {G'' H'' : Graph α'' β''} {a b c : α} {e f : β} {u v w : α'} {x y z : β''} {S S' T T' U U': Set α}
  {F F' R R' : Set β}
namespace Graph


structure Funs (G : Graph α β) (G' : Graph α' β') where
  toFun : V(G) → V(G')
  edgeFun : E(G) → E(G')

instance : CoeFun (Funs G G') fun (_ : Funs G G') ↦ V(G) → V(G') where
  coe v := v.toFun

@[simps]
def Funs.ofVxFun {G' : Graph α' β} (f : V(G) → V(G')) (hE : E(G) = E(G')) : Funs G G' where
  toFun := f
  edgeFun := fun ⟨e, he⟩ ↦ ⟨e, hE ▸ he⟩

@[simps]
def Funs.ofEdgeFun {G' : Graph α β'} (f : E(G) → E(G')) (hV : V(G) = V(G')) : Funs G G' where
  toFun := fun ⟨v, hv⟩ ↦ ⟨v, hV ▸ hv⟩
  edgeFun := f

@[simps]
def Funs.id : Funs G G where
  toFun := _root_.id
  edgeFun := _root_.id

@[simps]
def Funs.comp (f : Funs G G') (g : Funs G' G'') : Funs G G'' where
  toFun := g.toFun ∘ f.toFun
  edgeFun := g.edgeFun ∘ f.edgeFun

def Funs.of_le (hle : G ≤ H) : Funs G H where
  toFun v := ⟨v, vertexSet_subset_of_le hle v.prop⟩
  edgeFun e := ⟨e, edgeSet_subset_of_le hle e.prop⟩

lemma exists_funs (hV : V(G').Nonempty) (hE : E(G').Nonempty) : ∃ _ : Funs G G', True := by
  use {
    toFun := fun _ ↦ ⟨hV.some, hV.some_mem⟩
    edgeFun := fun _ ↦ ⟨hE.some, hE.some_mem⟩
  }

lemma edgeSet_eq_empty_of_Funs (F : Funs G G') (hE' : E(G') = ∅) : E(G) = ∅ := by
  simpa [hE'] using (⟨F.edgeFun⟩ : Nonempty (E(G) → E(G')))

lemma eq_noEdge_of_Funs (F : Funs G G') : G' = Graph.noEdge V(G') _ → G = Graph.noEdge V(G) _ := by
  simpa using edgeSet_eq_empty_of_Funs F



structure Hom (G : Graph α β) (G' : Graph α' β') extends Funs G G' where
  inc₂ ⦃e : E(G)⦄ ⦃x y : V(G)⦄ : G.Inc₂ e x y → G'.Inc₂ (edgeFun e) (toFun x) (toFun y)

  -- inc ⦃e : E(G)⦄ ⦃a : V(G)⦄ : G.Inc e a → G'.Inc (edgeFun e) (toFun a) := fun hinc ↦
  --   (inc₂ (inc_iff_exists_inc₂.mp hinc).choose_spec).inc_left
  -- toMultiset ⦃e : E(G)⦄ : (G.toMultiset e).map toFun = G'.toMultiset (edgeFun e) := by
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
def Hom.comp {G' : Graph α' β'} (f : Hom G G') (g : Hom G' G'') : Hom G G'' where
  toFuns := Funs.comp f.toFuns g.toFuns
  inc₂ _ _ _ hbtw := g.inc₂ (f.inc₂ hbtw)

def Hom.of_le (hle : G ≤ H) : Hom G H where
  toFuns := Funs.of_le hle
  inc₂ _ _ _ hbtw := hbtw.of_le hle

def HasHom (G₁ : Graph α β) (G₂ : Graph α' β') : Prop := Nonempty (Hom G₁ G₂)

scoped infix:50 " →ᴳ " => HasHom

lemma HasHom.rfl : G →ᴳ G := ⟨Hom.id⟩

lemma HasHom.trans (h₁₂ : G →ᴳ G') (h₂₃ : G' →ᴳ G'') : G →ᴳ G'' := by
  obtain ⟨f⟩ := h₁₂
  obtain ⟨g⟩ := h₂₃
  exact ⟨f.comp g⟩

lemma HasHom.of_le (hle : G ≤ H) : G →ᴳ H := ⟨Hom.of_le hle⟩

lemma hasHom_map {f : α → α'} {g : β → β'} (h : ∀ (e₁) (he₁ : e₁ ∈ E(G)) (e₂)
    (he₂ : e₂ ∈ E(G)), g e₁ = g e₂ → (G.toSym2 e₁ he₁).map f = (G.toSym2 e₂ he₂).map f)
    (hmap : G.map f g h ≤ G') : G →ᴳ G' := ⟨{
      toFun v := ⟨f v, vertexSet_subset_of_le hmap (mem_vertexSet_map v.prop)⟩
      edgeFun e := ⟨g e, edgeSet_subset_of_le hmap (mem_edgeSet_map e.prop)⟩
      inc₂ _ _ _ hbtw := hbtw.map.of_le hmap}⟩

lemma hasHom_iff_le_map [hα : Nonempty (α → α')] [hβ : Nonempty (β → β')] : G →ᴳ G' ↔
    ∃ (f : α → α') (g : β → β') (h : ∀ (e₁) (he₁ : e₁ ∈ E(G)) (e₂) (he₂ : e₂ ∈ E(G)), g e₁ = g e₂ →
    (G.toSym2 e₁ he₁).map f = (G.toSym2 e₂ he₂).map f), G.map f g h ≤ G' := by
  refine ⟨fun ⟨F⟩ ↦ ?_, fun ⟨f, g, h, heq⟩ ↦ hasHom_map h heq⟩
  use Function.extend Subtype.val (Subtype.val ∘ F.toFun) (Classical.arbitrary (α → α')),
    Function.extend Subtype.val (Subtype.val ∘ F.edgeFun) (Classical.arbitrary (β → β')), ?_, ?_, ?_
  · rintro e₁ he₁ e₂ he₂ h
    obtain ⟨x₁, y₁, hxy₁⟩ := exists_inc₂_of_mem_edgeSet he₁
    obtain ⟨x₂, y₂, hxy₂⟩ := exists_inc₂_of_mem_edgeSet he₂
    rw [Subtype.val_injective.extend_apply _ _ ⟨e₁, he₁⟩, Subtype.val_injective.extend_apply _ _ ⟨e₂, he₂⟩] at h
    rw [(toSym2_eq_pair_iff he₁).mpr hxy₁, (toSym2_eq_pair_iff he₂).mpr hxy₂, Sym2.map_pair_eq,
      Sym2.map_pair_eq, Subtype.val_injective.extend_apply _ _ ⟨x₁, hxy₁.vx_mem_left⟩,
      Subtype.val_injective.extend_apply _ _ ⟨y₁, hxy₁.vx_mem_right⟩,
      Subtype.val_injective.extend_apply _ _ ⟨x₂, hxy₂.vx_mem_left⟩,
      Subtype.val_injective.extend_apply _ _ ⟨y₂, hxy₂.vx_mem_right⟩]
    simp only [comp_apply, Subtype.val_inj] at h ⊢
    have hbtw₁ : G.Inc₂ (⟨e₁, he₁⟩ : E(G)) (⟨x₁, hxy₁.vx_mem_left⟩ : V(G)) (⟨y₁, hxy₁.vx_mem_right⟩ : V(G)) := hxy₁
    have hbtw₂ : G.Inc₂ (⟨e₂, he₂⟩ : E(G)) (⟨x₂, hxy₂.vx_mem_left⟩ : V(G)) (⟨y₂, hxy₂.vx_mem_right⟩ : V(G)) := hxy₂
    rw [← (toSym2_eq_pair_iff (F.edgeFun _).prop).mpr <| F.inc₂ hbtw₁, ← (toSym2_eq_pair_iff (F.edgeFun _).prop).mpr <| F.inc₂ hbtw₂]
    simp_rw [h]
  · rintro x hx
    simp only [map_vertexSet, mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Subtype.val_injective.extend_apply _ _ ⟨y, hy⟩]
    simp only [comp_apply, Subtype.coe_prop]
  · rintro e x y hxy
    simp only [map_inc₂] at hxy
    obtain ⟨e, rfl, x, rfl, y, rfl, hxy⟩ := hxy
    rw [Subtype.val_injective.extend_apply _ _ ⟨e, hxy.edge_mem⟩,
      Subtype.val_injective.extend_apply _ _ ⟨x, hxy.vx_mem_left⟩,
      Subtype.val_injective.extend_apply _ _ ⟨y, hxy.vx_mem_right⟩]
    simp only [comp_apply]
    exact F.inc₂ hxy



-- Todo: Add some stuff about cardinality


-- def HomSys.image (f : HomSys α β α' β') (h : f.IsHomOn G G₂) : Graph α' β' :=
--   ofInc (f '' V(G)) (fun e' v' ↦ ∃ e, f.edgeFun e = e' ∧ ∃ v, f v = v' ∧ G.Inc e v)
--   (by rintro e' v' ⟨e, rfl, v, rfl, hinc⟩; use v, hinc.vx_mem)
--   (by
--     rintro u' v' w' e' ⟨e, rfl, v, rfl, hincev⟩ ⟨a, heqae, b, rfl, hincab⟩ ⟨c, heqce, d, rfl, hinccd⟩
--     have hev := h.inc hincev
--     have hab := heqae ▸ h.inc hincab
--     have hcd := heqce ▸ h.inc hinccd
--     exact Inc.eq_or_eq_or_eq_of_inc_of_inc hev hab hcd)

-- @[simp] lemma HomSys.image_V (h : f.IsHomOn G G₂) : (f.image h).V = f '' V(G) :=
--   rfl

-- @[simp] lemma HomSys.image_E (h : f.IsHomOn G G₂) :
--     (f.image h).E = f.edgeFun '' E(G) := by
--   ext e'
--   simp only [image, ofInc_E, mem_setOf_eq, mem_image]
--   constructor
--   · rintro ⟨v, e, rfl, v, rfl, hinc⟩
--     use e, hinc.edge_mem
--   · rintro ⟨e, he, rfl⟩
--     obtain ⟨v, hinc⟩ := exists_inc_of_mem_edgeSet he
--     use f v, e, rfl, v

-- @[simp]
-- lemma HomSys.image_inc (h : f.IsHomOn G G₂) {e'} {v'}:
--     (f.image h).Inc e' v' ↔ ∃ e, f.edgeFun e = e' ∧ ∃ v, f v = v' ∧ G.Inc e v := by
--   simp only [image, ofInc_inc]

-- lemma HomSys.image_le (h : f.IsHomOn G G₂) : f.image h ≤ G₂ := by
--   rw [le_iff_inc, image_V, image_E]
--   refine ⟨image_subset_iff.mpr h.Mapsto_vx, image_subset_iff.mpr h.Mapsto_edge, ?_⟩
--   rintro e he v
--   simp only [image_inc]
--   constructor
--   · rintro ⟨e, rfl, v, rfl, hinc⟩
--     exact h.inc hinc
--   · rintro hinc
--     obtain ⟨b, hb, rfl⟩ := he
--     obtain ⟨a, a', hinc₂⟩ := exists_inc_of_mem_edgeSet hb
--     obtain (rfl | rfl) := (h.inc₂ hinc₂).eq_or_eq_of_inc hinc
--     · use b, rfl, a, rfl
--       exact hinc₂.inc_left
--     · use b, rfl, a', rfl
--       exact hinc₂.inc_right

-- lemma HomSys.image_isIsomOn (h : f.IsEmbOn G G₂) : f.IsIsomOn G (f.image h.toIsHomOn) where
--   Mapsto_vx v hv := by use v
--   inc₂ e v w hbtw := by
--     rw [← inc₂_iff_inc₂_of_le_of_mem (HomSys.image_le h.toIsHomOn)]
--     exact h.inc₂ hbtw
--     · simp only [image_E, mem_image]
--       use e, hbtw.edge_mem
--   bijOn_vx := ⟨fun u hu ↦ (by use u), fun u hu v hv heq ↦ h.injOn_vx hu hv heq, fun _ h ↦ h⟩
--   bijOn_edge := by
--     refine ⟨fun e he ↦ ?_, fun e he v hv heq ↦ h.injOn_edge he hv heq, fun d hd ↦ by
--       simpa only [image_E] using hd⟩
--     simp only [image_E, mem_image]
--     use e


structure Emb (G₁ : Graph α β) (G₂ : Graph α' β') extends Hom G₁ G₂ where
  inj_vx : Injective toFun
  inj_edge : Injective edgeFun

@[simps!]
def Emb.id : Emb G G where
  toHom := Hom.id
  inj_vx ⦃_ _⦄ h := h
  inj_edge ⦃_ _⦄ h := h

@[simps!]
def Emb.comp {G' : Graph α' β'} (f : Emb G G') (g : Emb G' G'') : Emb G G'' where
  toHom := Hom.comp f.toHom g.toHom
  inj_vx ⦃_ _⦄ h := f.inj_vx (g.inj_vx h)
  inj_edge ⦃_ _⦄ h := f.inj_edge (g.inj_edge h)

def HasEmb (G₁ : Graph α β) (G₂ : Graph α' β') : Prop := Nonempty (Emb G₁ G₂)

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
    toFun v := ⟨v, vertexSet_subset_of_le hle v.prop⟩
    edgeFun e := ⟨e, edgeSet_subset_of_le hle e.prop⟩
    inc₂ e x y hbtw := hbtw.of_le hle
    inj_vx x y h := by
      simp only [Subtype.mk.injEq] at h
      exact SetCoe.ext h
    inj_edge e f h := by
      simp only [Subtype.mk.injEq] at h
      exact SetCoe.ext h
  }⟩

lemma HasEmb.bot : (⊥ : Graph α β) ↪ᴳ G' := ⟨{
    toFun v := IsEmpty.elim (α := (∅ : Set α).Elem) inferInstance v
    edgeFun e := IsEmpty.elim (α := (∅ : Set β).Elem) inferInstance e
    inc₂ e := IsEmpty.elim (α := (∅ : Set β).Elem) inferInstance e
    inj_vx v := IsEmpty.elim (α := (∅ : Set α).Elem) inferInstance v
    inj_edge e := IsEmpty.elim (α := (∅ : Set β).Elem) inferInstance e
  }⟩

lemma eq_bot_of_hasEmb_bot (h : G ↪ᴳ (⊥ : Graph α' β')) : G = ⊥ := by
  obtain ⟨f⟩ := h
  have : Nonempty (V(G) → V(⊥)) := ⟨f.toFun⟩
  simpa using this

-- lemma map_hasEmb
-- lemma hasEmb_iff_le_map



structure Isom (G₁ : Graph α β) (G₂ : Graph α' β') extends Hom G₁ G₂ where
  invFun : V(G₂) → V(G₁)
  vx_right_inv : RightInverse invFun toFun
  vx_left_inv : LeftInverse invFun toFun
  edgeInvFun : E(G₂) → E(G₁)
  edge_right_inv : RightInverse edgeInvFun edgeFun
  edge_left_inv : LeftInverse edgeInvFun edgeFun

lemma Isom.inc₂_iff (f : Isom G G') {e : E(G)} {x y : V(G)} :
    G.Inc₂ e x y ↔ G'.Inc₂ (f.edgeFun e) (f.toFun x) (f.toFun y) := by
  refine ⟨(f.inc₂ ·), fun h ↦ ?_⟩
  obtain ⟨u, v, huv⟩ := exists_inc₂_of_mem_edgeSet e.prop
  have huv' : G.Inc₂ e (⟨u, huv.vx_mem_left⟩ : V(G)) (⟨v, huv.vx_mem_right⟩ : V(G)) := huv
  obtain ⟨hu, hv⟩ | ⟨hu, hv⟩ := (f.inc₂ huv').eq_and_eq_or_eq_and_eq_of_inc₂ h <;>
  rw [← Subtype.eq_iff, f.vx_left_inv.injective.eq_iff] at hu hv <;>
  subst x y
  · exact huv
  · exact huv.symm

alias ⟨Inc₂.isIsomOn, _⟩ := Isom.inc₂_iff

lemma Isom.inc₂_iff' (F : Isom G G') {e : E(G')} {x y : V(G')} :
    G'.Inc₂ e x y ↔ G.Inc₂ (F.edgeInvFun e) (F.invFun x) (F.invFun y) := by
  conv_lhs => rw [← F.edge_right_inv e, ← F.vx_right_inv x, ← F.vx_right_inv y, ← F.inc₂_iff]

lemma Isom.inj_vx (f : Isom G G') : Injective f.toFun := f.vx_left_inv.injective
lemma Isom.surj_vx (f : Isom G G') : Surjective f.toFun := f.vx_right_inv.surjective
lemma Isom.inv_inj_vx (f : Isom G G') : Injective f.invFun := f.vx_right_inv.injective
lemma Isom.surj_inv_vx (f : Isom G G') : Surjective f.invFun := f.vx_left_inv.surjective
lemma Isom.inj_edge (f : Isom G G') : Injective f.edgeFun := f.edge_left_inv.injective
lemma Isom.surj_edge (f : Isom G G') : Surjective f.edgeFun := f.edge_right_inv.surjective
lemma Isom.inv_inj_edge (f : Isom G G') : Injective f.edgeInvFun := f.edge_right_inv.injective
lemma Isom.surj_inv_edge (f : Isom G G') : Surjective f.edgeInvFun := f.edge_left_inv.surjective

lemma Isom.bij_vx (f : Isom G G') : Bijective f.toFun := by
  rw [Function.bijective_iff_has_inverse]
  exact ⟨f.invFun, f.vx_left_inv, f.vx_right_inv⟩

lemma Isom.bij_edge (f : Isom G G') : Bijective f.edgeFun := by
  rw [Function.bijective_iff_has_inverse]
  exact ⟨f.edgeInvFun, f.edge_left_inv, f.edge_right_inv⟩

lemma Isom.bij_inv_vx (f : Isom G G') : Bijective f.invFun := by
  rw [Function.bijective_iff_has_inverse]
  exact ⟨f.toFun, f.vx_right_inv, f.vx_left_inv⟩

lemma Isom.bij_inv_edge (f : Isom G G') : Bijective f.edgeInvFun := by
  rw [Function.bijective_iff_has_inverse]
  exact ⟨f.edgeFun, f.edge_right_inv, f.edge_left_inv⟩

def Isom.toInvHom (f : Isom G G') : Hom G' G where
  toFun := f.invFun
  edgeFun := f.edgeInvFun
  inc₂ _ _ _ hbtw := f.inc₂_iff'.mp hbtw

def Isom.toEmb (f : Isom G G') : Emb G G' where
  toHom := f.toHom
  inj_vx := f.inj_vx
  inj_edge := f.inj_edge

def Isom.vxEquiv (f : Isom G G') : V(G) ≃ V(G') where
  toFun := f.toFun
  invFun := f.invFun
  left_inv := f.vx_left_inv
  right_inv := f.vx_right_inv

def Isom.edgeEquiv (f : Isom G G') : E(G) ≃ E(G') where
  toFun := f.edgeFun
  invFun := f.edgeInvFun
  left_inv := f.edge_left_inv
  right_inv := f.edge_right_inv

noncomputable def Isom.ofSurjEmb (f : Emb G G') (hvxSurj : Surjective f.toFun) (hedgeSurj : Surjective f.edgeFun) : Isom G G' where
  toHom := f.toHom
  invFun := by
    by_cases h : Nonempty V(G).Elem
    · exact f.toFun.invFun
    · simp only [nonempty_subtype, not_exists] at h
      rintro v
      simpa using h (hvxSurj v).choose
  vx_right_inv v := by
    by_cases h : Nonempty V(G).Elem
    · simp only [h, ↓reduceDIte]
      exact invFun_eq (hvxSurj _)
    · simp only [nonempty_subtype, not_exists] at h
      simpa using h (hvxSurj v).choose
  vx_left_inv v := by
    by_cases h : Nonempty V(G).Elem
    · simp only [h, ↓reduceDIte]
      refine congrFun (invFun_comp f.inj_vx) _
    · simp only [nonempty_subtype, not_exists] at h
      simpa using h v
  edgeInvFun := by
    by_cases h : Nonempty E(G).Elem
    · exact f.edgeFun.invFun
    · simp only [nonempty_subtype, not_exists] at h
      rintro e
      simpa using h (hedgeSurj e).choose
  edge_right_inv e := by
    by_cases h : Nonempty E(G).Elem
    · simp only [h, ↓reduceDIte]
      exact invFun_eq (hedgeSurj e)
    · simp only [nonempty_subtype, not_exists] at h
      simpa using h (hedgeSurj e).choose
  edge_left_inv e := by
    by_cases h : Nonempty E(G).Elem
    · simp only [h, ↓reduceDIte]
      exact congrFun (invFun_comp f.inj_edge) _
    · simp only [nonempty_subtype, not_exists] at h
      simpa using h e

noncomputable def Isom.ofEmbCard [Finite V(G')] [Finite E(G')] (f : Emb G G')
    (hVcard : Nat.card V(G') ≤ Nat.card V(G)) (hedgeCard : Nat.card E(G') ≤ Nat.card E(G)) : Isom G G' :=
  Isom.ofSurjEmb f (Function.Injective.bijective_of_nat_card_le f.inj_vx hVcard).surjective
    (Function.Injective.bijective_of_nat_card_le f.inj_edge hedgeCard).surjective

def Isom.ofEquiv (f : V(G) ≃ V(G')) (g : E(G) ≃ E(G'))
    (hinc₂ : ∀ (e : E(G)) (x y : V(G)), G.Inc₂ e x y → G'.Inc₂ (g e) (f x) (f y)) : Isom G G' where
  toFun := f.toFun
  edgeFun := g.toFun
  invFun := f.invFun
  vx_right_inv := f.right_inv
  vx_left_inv := f.left_inv
  edgeInvFun := g.invFun
  edge_right_inv := g.right_inv
  edge_left_inv := g.left_inv
  inc₂ := hinc₂

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
def Isom.symm (f : Isom G G') : Isom G' G where
  toFun := f.invFun
  invFun := f.toFun
  edgeFun := f.edgeInvFun
  edgeInvFun := f.edgeFun
  vx_right_inv := f.vx_left_inv
  vx_left_inv := f.vx_right_inv
  edge_right_inv := f.edge_left_inv
  edge_left_inv := f.edge_right_inv
  inc₂ e x y hbtw := by
    obtain ⟨e', rfl⟩ := f.edge_right_inv.surjective e
    obtain ⟨x', rfl⟩ := f.vx_right_inv.surjective x
    obtain ⟨y', rfl⟩ := f.vx_right_inv.surjective y
    rwa [f.edge_left_inv e', f.vx_left_inv x', f.vx_left_inv y', f.inc₂_iff]

@[simps!]
def Isom.comp {G' : Graph α' β'} (f : Isom G G') (g : Isom G' G'') : Isom G G'' where
  toHom := Hom.comp f.toHom g.toHom
  invFun := f.invFun ∘ g.invFun
  vx_right_inv x := by
    simp only [Hom.comp_toFun, comp_apply, g.vx_right_inv x, f.vx_right_inv (g.invFun x)]
  vx_left_inv x := by
    simp only [Hom.comp_toFun, comp_apply, g.vx_left_inv (f.toFun x), f.vx_left_inv x]
  edgeInvFun := f.edgeInvFun ∘ g.edgeInvFun
  edge_right_inv e := by
    simp only [Hom.comp_edgeFun, comp_apply, g.edge_right_inv e, f.edge_right_inv (g.edgeInvFun e)]
  edge_left_inv e := by
    simp only [Hom.comp_edgeFun, comp_apply, g.edge_left_inv (f.edgeFun e), f.edge_left_inv e]

noncomputable def vxMap_inj_isom (f : α → α') (hinj : InjOn f V(G)) : Isom G (f '' G) where
  toFun v := ⟨f v, (vxMap_vertexSet G f) ▸ ⟨v, v.prop, rfl⟩⟩
  edgeFun e := ⟨e, by simp⟩
  invFun v := ⟨v.prop.choose, v.prop.choose_spec.1⟩
  edgeInvFun e := ⟨e, by simpa using e.prop⟩
  vx_right_inv v := by
    rw [Subtype.ext_iff]
    exact v.prop.choose_spec.2
  vx_left_inv v := by
    rw [Subtype.ext_iff]
    have : f ↑v ∈ f '' V(G) := ⟨v, v.prop, rfl⟩
    exact hinj this.choose_spec.1 v.prop this.choose_spec.2
  edge_right_inv e := by
    rw [Subtype.ext_iff]
  edge_left_inv e := by
    rw [Subtype.ext_iff]
  inc₂ e x y hbtw := by
    rw [vxMap_inc₂]
    exact ⟨x, rfl, y, rfl, hbtw⟩

def edgeMap_isom (f : β → β') (hf : InjOn f E(G)) : Isom G (G.edgeMap f hf) := sorry


def HasIsom (G₁ : Graph α β) (G₂ : Graph α' β') : Prop := Nonempty (Isom G₁ G₂)

scoped infix:50 " ↔ᴳ " => HasIsom

lemma HasIsom.toHasEmb (h : HasIsom G G') : G ↪ᴳ G' := by
  obtain ⟨f⟩ := h
  exact ⟨f.toEmb⟩

lemma HasIsom.toHasHom (h : HasIsom G G') : G →ᴳ G' := by
  obtain ⟨f⟩ := h
  exact ⟨f.toHom⟩

@[simp] lemma HasIsom.vxEquiv (h : G ↔ᴳ G') : Nonempty (V(G) ≃ V(G')) := ⟨h.some.vxEquiv⟩

@[simp] lemma HasIsom.edgeEquiv (h : G ↔ᴳ G') : Nonempty (E(G) ≃ E(G')) := ⟨h.some.edgeEquiv⟩

lemma HasIsom.rfl : G ↔ᴳ G := ⟨Isom.id⟩

lemma HasIsom.symm (h : G ↔ᴳ G') : G' ↔ᴳ G := by
  obtain ⟨f⟩ := h
  exact ⟨f.symm⟩

lemma HasIsom.trans (h₁₂ : G ↔ᴳ G') (h₂₃ : G' ↔ᴳ G'') : G ↔ᴳ G'' := by
  obtain ⟨f⟩ := h₁₂
  obtain ⟨g⟩ := h₂₃
  exact ⟨f.comp g⟩

lemma HasIsom.ofEmbCard [Finite V(G')] [Finite E(G')] (f : G ↪ᴳ G')
    (hVcard : Nat.card V(G') ≤ Nat.card V(G)) (hedgeCard : Nat.card E(G') ≤ Nat.card E(G)) : G ↔ᴳ G' :=
  let ⟨f⟩ := f
  ⟨Isom.ofEmbCard f hVcard hedgeCard⟩

lemma vxMap_hasIsom {f : α → α'} (hinj : InjOn f V(G)) : G ↔ᴳ G.vxMap f :=
  ⟨vxMap_inj_isom f hinj⟩

lemma edgeMap_hasIsom {f : β → β'} (hf : InjOn f E(G)) : G ↔ᴳ G.edgeMap f hf :=
  ⟨edgeMap_isom f hf⟩

lemma bot_hasIsom_bot : (⊥ : Graph α β) ↔ᴳ (⊥ : Graph α' β') := HasIsom.ofEmbCard HasEmb.bot
  (by simp) (by simp)

-- lemma bot_hasIsom_iff : (⊥ : Graph α' β') ↔ᴳ G ↔ G = ⊥ := by
--   constructor
--   · rintro ⟨f⟩
--     have := hf.bijOn_vx.surjOn
--     simpa using this
--   · rintro rfl
--     exact bot_hasIsom_bot

@[simp]
lemma noEdge_hasIsom_noEdge_iff {T : Set α'} : Graph.noEdge S β ↔ᴳ Graph.noEdge T β' ↔ Nonempty (S ≃ T) := by
  refine ⟨fun h ↦ h.vxEquiv, fun ⟨F⟩ ↦ ⟨?_⟩⟩
  refine Isom.ofEquiv (by simpa) ?_ (by simp)
  rw [noEdge_edgeSet]
  exact Equiv.equivOfIsEmpty _ _

noncomputable def isom_map {f : α → α'} {g : β → β'} (h : ∀ (e₁) (he₁ : e₁ ∈ E(G)) (e₂)
    (he₂ : e₂ ∈ E(G)), g e₁ = g e₂ → (G.toSym2 e₁ he₁).map f = (G.toSym2 e₂ he₂).map f)
    (hvInj : InjOn f V(G)) (heInj : InjOn g E(G))
    (hmap : G.map f g h = G') : Isom G G' := by
  let fᵥ : V(G) → V(G') := fun v ↦ ⟨f v, vertexSet_subset_of_le hmap.le (mem_vertexSet_map v.prop)⟩
  let fₑ : E(G) → E(G') := fun e ↦ ⟨g e, edgeSet_subset_of_le hmap.le (mem_edgeSet_map e.prop)⟩
  subst G'
  have hfᵥ : Function.Bijective fᵥ := by
    refine ⟨fun u v h ↦ ?_, fun v ↦ ?_⟩
    · rw [Subtype.ext_iff]
      refine hvInj u.prop v.prop ?_
      simpa [fᵥ] using h
    · simp only [map_vertexSet, Subtype.exists, fᵥ]
      obtain ⟨v, v, hv, rfl⟩ := v
      use v, hv
  have hfₑ : Function.Bijective fₑ := by
    refine ⟨fun e₁ e₂ h ↦ ?_, fun e ↦ ?_⟩
    · simpa [fₑ, heInj.eq_iff, Subtype.ext_iff] using h
    · simp only [map_edgeSet, Subtype.exists, fₑ]
      obtain ⟨e', he'⟩ := e
      simp only [map_edgeSet, mem_image, fᵥ, fₑ] at he'
      obtain ⟨e, he, rfl⟩ := he'
      simp only [map_edgeSet, mem_image, fᵥ, fₑ] at he'
      obtain ⟨a, ha, heq⟩ := he'
      use a, ha, by simp_rw [heq]
  exact {
    toFun := fᵥ
    edgeFun := fₑ
    inc₂ _ _ _ hbtw := hbtw.map.of_le le_rfl
    invFun := surjInv hfᵥ.surjective
    vx_right_inv := rightInverse_surjInv hfᵥ.surjective
    vx_left_inv := leftInverse_surjInv hfᵥ
    edgeInvFun := surjInv hfₑ.surjective
    edge_right_inv := rightInverse_surjInv hfₑ.surjective
    edge_left_inv := leftInverse_surjInv hfₑ}

lemma hasIsom_iff_eq_map [hα : Nonempty (α → α')] [hβ : Nonempty (β → β')] : G ↔ᴳ G' ↔
    ∃ (f : α → α') (g : β → β') (h : ∀ (e₁) (he₁ : e₁ ∈ E(G)) (e₂) (he₂ : e₂ ∈ E(G)), g e₁ = g e₂ →
    (G.toSym2 e₁ he₁).map f = (G.toSym2 e₂ he₂).map f), InjOn f V(G) ∧ InjOn g E(G) ∧ G.map f g h = G' := by
  refine ⟨fun ⟨F⟩ ↦ ?_, fun ⟨f, g, h, hvInj, heInj, heq⟩ ↦ ⟨isom_map h hvInj heInj heq⟩⟩
  use extend Subtype.val (Subtype.val ∘ F.toFun) (Classical.arbitrary (α → α')),
    extend Subtype.val (Subtype.val ∘ F.edgeFun) (Classical.arbitrary (β → β')), ?_, ?_, ?_, ?_
  · rintro e₁ he₁ e₂ he₂ h
    obtain ⟨x₁, y₁, hxy₁⟩ := exists_inc₂_of_mem_edgeSet he₁
    obtain ⟨x₂, y₂, hxy₂⟩ := exists_inc₂_of_mem_edgeSet he₂
    rw [Subtype.val_injective.extend_apply _ _ ⟨e₁, he₁⟩, Subtype.val_injective.extend_apply _ _ ⟨e₂, he₂⟩] at h
    rw [(toSym2_eq_pair_iff he₁).mpr hxy₁, (toSym2_eq_pair_iff he₂).mpr hxy₂, Sym2.map_pair_eq,
      Sym2.map_pair_eq, Subtype.val_injective.extend_apply _ _ ⟨x₁, hxy₁.vx_mem_left⟩,
      Subtype.val_injective.extend_apply _ _ ⟨y₁, hxy₁.vx_mem_right⟩,
      Subtype.val_injective.extend_apply _ _ ⟨x₂, hxy₂.vx_mem_left⟩,
      Subtype.val_injective.extend_apply _ _ ⟨y₂, hxy₂.vx_mem_right⟩]
    simp only [comp_apply, Subtype.val_inj] at h ⊢
    have hbtw₁ : G.Inc₂ (⟨e₁, he₁⟩ : E(G)) (⟨x₁, hxy₁.vx_mem_left⟩ : V(G)) (⟨y₁, hxy₁.vx_mem_right⟩ : V(G)) := hxy₁
    have hbtw₂ : G.Inc₂ (⟨e₂, he₂⟩ : E(G)) (⟨x₂, hxy₂.vx_mem_left⟩ : V(G)) (⟨y₂, hxy₂.vx_mem_right⟩ : V(G)) := hxy₂
    rw [← (toSym2_eq_pair_iff (F.edgeFun _).prop).mpr <| F.inc₂ hbtw₁, ← (toSym2_eq_pair_iff (F.edgeFun _).prop).mpr <| F.inc₂ hbtw₂]
    simp_rw [h]
  · rintro u hu v hv h
    rwa [Subtype.val_injective.extend_apply _ _ ⟨u, hu⟩, Subtype.val_injective.extend_apply _ _ ⟨v, hv⟩,
      comp_apply, comp_apply, Subtype.val_inj, F.inj_vx.eq_iff, ← Subtype.val_inj] at h
  · rintro e₁ he₁ e₂ he₂ h
    rwa [Subtype.val_injective.extend_apply _ _ ⟨e₁, he₁⟩, Subtype.val_injective.extend_apply _ _ ⟨e₂, he₂⟩,
      comp_apply, comp_apply, Subtype.val_inj, F.inj_edge.eq_iff, ← Subtype.val_inj] at h
  · ext a b c
    · simp only [map_vertexSet, mem_image]
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [Subtype.val_injective.extend_apply _ _ ⟨u, hu⟩, comp_apply]
        exact Subtype.coe_prop (F.toFun ⟨u, hu⟩)
      · rintro h
        use F.invFun ⟨a, h⟩, Subtype.coe_prop (F.invFun ⟨a, h⟩)
        rw [Subtype.val_injective.extend_apply _ _ (F.invFun ⟨a, h⟩), comp_apply, F.vx_right_inv]
    · simp only [map_inc₂]
      constructor
      · rintro ⟨e, rfl, x, rfl, y, rfl, hbtw⟩
        rw [Subtype.val_injective.extend_apply _ _ ⟨e, hbtw.edge_mem⟩,
          Subtype.val_injective.extend_apply _ _ ⟨x, hbtw.vx_mem_left⟩,
          Subtype.val_injective.extend_apply _ _ ⟨y, hbtw.vx_mem_right⟩,
          comp_apply, comp_apply, comp_apply]
        exact F.inc₂ hbtw
      · rintro hbtw
        use F.edgeInvFun ⟨a, hbtw.edge_mem⟩, ?_, F.invFun ⟨b, hbtw.vx_mem_left⟩, ?_, F.invFun ⟨c, hbtw.vx_mem_right⟩, ?_, ?_
        · rw [Subtype.val_injective.extend_apply _ _ (F.edgeInvFun ⟨_, hbtw.edge_mem⟩), comp_apply, F.edge_right_inv]
        · rw [Subtype.val_injective.extend_apply _ _ (F.invFun ⟨_, hbtw.vx_mem_left⟩), comp_apply, F.vx_right_inv]
        · rw [Subtype.val_injective.extend_apply _ _ (F.invFun ⟨_, hbtw.vx_mem_right⟩), comp_apply, F.vx_right_inv]
        · rwa [← F.inc₂_iff']

structure vertexPermutation (G₁ : Graph α β) (G₂ : Graph α' β) extends Isom G₁ G₂ where
  edgeFun_id : Subtype.val ∘ edgeFun = Subtype.val

variable {G : Graph α β} {G' : Graph α' β}

lemma vertexPermutation.edgeInvFun_id (F : vertexPermutation G G') :
    Subtype.val ∘ F.edgeInvFun = Subtype.val := by
  rw [← F.edgeFun_id, comp_assoc, F.edge_right_inv.comp_eq_id, comp_id]

-- noncomputable def vxMap_vertexPermutation (f : α → α') : vertexPermutation G (f '' G) where


variable {α α' α'' α''' β β' β'' β''' χ χ' χ'' χ''' : Type*}
  {G : Graph α β} {G' : Graph α' β'} {H : Graph α'' β''} {H' : Graph α''' β'''}
universe u₀ u₁ u₂ v₀ v₁ v₂

class GraphicFunction (f : outParam <| ∀ {α : Type u₀} {β : Type v₀}, Graph α β → χ)
    (g : ∀ {α : Type u₁} {β : Type v₁}, Graph α β → χ) where
  invariant {α₁ β₁ α₂ β₂} {G : Graph α₁ β₁} {G' : Graph α₂ β₂} : G ↔ᴳ G' → f G = g G'

-- lemma iff_exists_isom (f : ∀ {α : Type u₀} {β : Type v₀}, Graph α β → Prop)
--     (g : ∀ {α : Type (max u₀ u₁)} {β : Type (max v₀ v₁)}, Graph α β → Prop)
--     [hP : GraphicFunction f g] {α : Type u₀} {β : Type v₀} {G : Graph α β} :
--     f G ↔ ∃ (α' : Type (max u₀ u₁)) (β' : Type (max v₀ v₁))
--     (G' : Graph α' β'), g G' ∧ G ↔ᴳ G' := by
--   constructor
--   · rintro h
--     use ULift α, ULift β
--     sorry
--     -- exact ⟨h, HasIsom.rfl⟩
--   · rintro ⟨α', β', G', hg, h'⟩
--     rwa [hP.invariant h']

scoped notation F "|₂" B => F B B

variable {α : Type u₀} {β : Type v₀} {α' : Type u₁} {β' : Type v₁}
  {G : Graph α β} {G' : Graph α' β'}
  {A : {α : Type u₀} → {β : Type v₀} → (G : Graph α β) → χ}
  {A₁ : {α : Type u₁} → {β : Type v₁} → (G : Graph α β) → χ}
  {A' : {α : Type u₀} → {β : Type v₀} → (G : Graph α β) → χ'}
  {A'₁ : {α : Type u₁} → {β : Type v₁} → (G : Graph α β) → χ'}
  {A'' : {α : Type u₀} → {β : Type v₀} → (G : Graph α β) → χ''}
  {A''₁ : {α : Type u₁} → {β : Type v₁} → (G : Graph α β) → χ''}
  {P Q : {α : Type u₀} → {β : Type v₀} → (G : Graph α β) → Prop}
  {P₁ Q₁ : {α : Type u₁} → {β : Type v₁} → (G : Graph α β) → Prop}
  [hA : GraphicFunction A A₁] [hA' : GraphicFunction A' A'₁] [hA'' : GraphicFunction A'' A''₁]
  [hP : GraphicFunction P P₁] [hQ : GraphicFunction Q Q₁]

lemma HasIsom.eq (h : G ↔ᴳ G') (A : {α : Type u₀} → {β : Type v₀} → (G : Graph α β) → χ)
    (A₁ : {α : Type u₁} → {β : Type v₁} → (G : Graph α β) → χ) [hA : GraphicFunction A A₁] :
    A G = A₁ G' := hA.invariant h

lemma HasIsom.iff (h : G ↔ᴳ G') (P : {α : Type u₀} → {β : Type v₀} → (G : Graph α β) → Prop)
    (P₁ : {α : Type u₁} → {β : Type v₁} → (G : Graph α β) → Prop) [hP : GraphicFunction P P₁] :
    P G ↔ P₁ G' := by
  rw [← hP.invariant h]

instance instConstGraphic (c : χ) : GraphicFunction |₂ (fun _ ↦ c) where
  invariant _ := rfl

instance instCompGraphic (f : χ' → χ) : GraphicFunction (fun G ↦ f (A' G)) (fun G ↦ f (A'₁ G)) where
  invariant h := by rw [← hA'.invariant h]

instance instComp2Graphic (f : χ → χ' → χ'') :
    GraphicFunction (fun G ↦ f (A G) (A' G)) (fun G ↦ f (A₁ G) (A'₁ G)) where
  invariant h := by rw [← hA.invariant h, ← hA'.invariant h]

instance instComp3Graphic (f : χ → χ' → χ'' → χ''') :
    GraphicFunction (fun G ↦ f (A G) (A' G) (A'' G)) (fun G ↦ f (A₁ G) (A'₁ G) (A''₁ G)) where
  invariant h := by rw [← hA.invariant h, ← hA'.invariant h, ← hA''.invariant h]

instance instImpGraphic : GraphicFunction (fun G ↦ P G → Q G) (fun G ↦ P₁ G → Q₁ G) :=
  instComp2Graphic (· → ·)

instance instHasIsomLeftGraphic : GraphicFunction |₂ (fun G ↦ G ↔ᴳ H) where
  invariant h := by
    rw [eq_iff_iff]
    exact ⟨h.symm.trans, h.trans⟩

instance instHasIsomRightGraphic : GraphicFunction |₂ (fun G ↦ H ↔ᴳ G) where
  invariant h := by
    rw [eq_iff_iff]
    exact ⟨(HasIsom.trans · h), (HasIsom.trans · h.symm)⟩

instance instHasEmbLeftGraphic : GraphicFunction |₂ (fun G ↦ G ↪ᴳ H) where
  invariant h := by
    rw [eq_iff_iff]
    exact ⟨h.symm.toHasEmb.trans, h.toHasEmb.trans⟩

instance instHasEmbRightGraphic : GraphicFunction |₂ (fun G ↦ H ↪ᴳ G) where
  invariant h := by
    rw [eq_iff_iff]
    exact ⟨(HasEmb.trans · h.toHasEmb), (HasEmb.trans · h.symm.toHasEmb)⟩

instance instHasHomLeftGraphic : GraphicFunction |₂ (fun G ↦ G →ᴳ H) where
  invariant h := by
    rw [eq_iff_iff]
    exact ⟨h.symm.toHasHom.trans, h.toHasHom.trans⟩

instance instHasHomRightGraphic : GraphicFunction |₂ (fun G ↦ H →ᴳ G) where
  invariant h := by
    rw [eq_iff_iff]
    exact ⟨(HasHom.trans · h.toHasHom), (HasHom.trans · h.symm.toHasHom)⟩

instance instVxSetFiniteGraphic : GraphicFunction |₂ (fun G ↦ Finite V(G)) where
  invariant h := by
    rw [eq_iff_iff]
    obtain ⟨f⟩ := h
    exact f.bij_vx.finite_iff

instance instEdgeSetFiniteGraphic : GraphicFunction |₂ (fun G ↦ Finite E(G)) where
  invariant h := by
    rw [eq_iff_iff]
    obtain ⟨f⟩ := h
    exact f.bij_edge.finite_iff

instance instVxSetNonemptyGraphic : GraphicFunction |₂ (fun G ↦ V(G).Nonempty) where
  invariant h := by
    rw [eq_iff_iff]
    obtain ⟨f⟩ := h
    simpa only [nonempty_subtype] using f.bij_vx.nonempty_iff

instance instEdgeSetNonemptyGraphic : GraphicFunction |₂ (fun G ↦ E(G).Nonempty) where
  invariant h := by
    rw [eq_iff_iff]
    obtain ⟨f⟩ := h
    simpa only [nonempty_subtype] using f.bij_edge.nonempty_iff

instance instVxSetEncardGraphic : GraphicFunction |₂ (fun G ↦ V(G).encard) where
  invariant h := by
    obtain ⟨f⟩ := h
    have := f.bij_vx
    sorry
    -- exact bijOn_encard this

instance instEdgeSetEncardGraphic : GraphicFunction |₂ (fun G ↦ E(G).encard) where
  invariant h := by
    obtain ⟨f⟩ := h
    have := f.bij_edge
    sorry
    -- exact bijOn_encard this

instance instVxSetNcardGraphic : GraphicFunction |₂ (fun G ↦ V(G).ncard) where
  invariant h := by
    obtain ⟨f⟩ := h
    exact Nat.card_eq_of_bijective _ f.bij_vx

instance instEdgeSetNcardGraphic : GraphicFunction |₂ (fun G ↦ E(G).ncard) where
  invariant h := by
    obtain ⟨f⟩ := h
    exact Nat.card_eq_of_bijective _ f.bij_edge

instance instEqBotGraphic : GraphicFunction |₂ (fun G ↦ G = ⊥) where
  invariant h := by
    simp only [eq_iff_iff]
    rw [← vertexSet_empty_iff_eq_bot, ← vertexSet_empty_iff_eq_bot]
    have := instVxSetNonemptyGraphic.invariant h
    rwa [eq_iff_iff, ← not_iff_not, not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty] at this

instance instEqNoEdgeGraphic : GraphicFunction |₂ (fun G ↦ G = Graph.noEdge V(G) _) where
  invariant h := by
    simp only [eq_iff_iff]
    rw [← edgeSet_empty_iff_eq_noEdge, ← edgeSet_empty_iff_eq_noEdge]
    have := instEdgeSetNonemptyGraphic.invariant h
    rwa [eq_iff_iff, ← not_iff_not, not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty] at this

lemma forall_type_nonempty {P : {α : Type u₀} → {β : Type v₀} → (G : Graph α β) → Prop}
    [hP : GraphicFunction P P] (h : ∀ {α β : Type _} [Nonempty α] [Nonempty β] (G : Graph α β), P G)
    {α β : Type _} : ∀ (G : Graph α β), P G := by
  intro G
  obtain (hα | hα) := isEmpty_or_nonempty α
  · rw [eq_bot_of_isEmpty (G := G), ← hP.invariant (bot_hasIsom_bot) (α₁ := PUnit) (β₁ := PUnit)]
    exact h ⊥

  obtain (hβ | hβ) := isEmpty_or_nonempty β
  · rw [eq_noEdge_of_isEmpty (G := G), ← hP.invariant (noEdge_hasIsom_noEdge_iff.mpr ⟨Equiv.refl _⟩) (β₁ := PUnit)]
    exact h _

  exact h G


-- Change this to allow the IsEmpty case
class GraphicVertexFunction (f : outParam <| ∀ {β : Type v₀} (_ : Graph α β), χ)
    (g : ∀ {β : Type v₁} (_ : Graph α β), χ) : Prop where
  invariant {β₁ β₂} {G : Graph α β₁} {G' : Graph α β₂} :
    (∃ (F : Isom G G'), Subtype.val ∘ F.toFun = Subtype.val) → f G = g G'

-- WHY IS THIS NOT WORKING?
instance instGraphicGraphicVertex {A : ∀ {α : Type u₀} {β : Type v₀}, Graph α β → χ}
    {B : ∀ {α : Type u₀} {β : Type v₁}, Graph α β → χ}
    [hF : GraphicFunction A B] : GraphicVertexFunction (fun G ↦ A (α := α) G) (fun G ↦ B (α := α) G) where
  invariant h := by
    obtain ⟨F, hF⟩ := h
    exact HasIsom.eq ⟨F⟩ A B

example : GraphicVertexFunction (fun (G : Graph α _) ↦ V(G).ncard) (fun (G : Graph α _) ↦ V(G).ncard) :=
  -- inferInstance
  instGraphicGraphicVertex (hF := instVxSetNcardGraphic)

variable {A : {β : Type v₀} → (G : Graph α β) → χ}
  {A₁ : {β : Type v₁} → (G : Graph α β) → χ}
  {A' : {β : Type v₀} → (G : Graph α β) → χ'}
  {A'₁ : {β : Type v₁} → (G : Graph α β) → χ'}
  {A'' : {β : Type v₀} → (G : Graph α β) → χ''}
  {A''₁ : {β : Type v₁} → (G : Graph α β) → χ''}
  {P Q : {β : Type v₀} → (G : Graph α β) → Prop}
  {P₁ Q₁ : {β : Type v₁} → (G : Graph α β) → Prop}
  [hA : GraphicVertexFunction A A₁] [hA' : GraphicVertexFunction A' A'₁] [hA'' : GraphicVertexFunction A'' A''₁]
  [hP : GraphicVertexFunction P P₁] [hQ : GraphicVertexFunction Q Q₁]

instance instConstGraphicVertex (c : χ) : GraphicVertexFunction |₂ (fun (_ : Graph α _) ↦ c) :=
  instGraphicGraphicVertex (hF := instConstGraphic c)

instance instCompGraphicVertex (f : χ' → χ) :
    GraphicVertexFunction (fun (G : Graph α _) ↦ f (A' G)) (fun (G : Graph α _) ↦ f (A'₁ G)) where
  invariant h := by rw [← hA'.invariant h]

instance instComp2GraphicVertex (f : χ → χ' → χ'') :
    GraphicVertexFunction (fun (G : Graph α _) ↦ f (A G) (A' G)) (fun (G : Graph α _) ↦ f (A₁ G) (A'₁ G)) where
  invariant h := by rw [← hA.invariant h, ← hA'.invariant h]

instance instComp3GraphicVertex (f : χ → χ' → χ'' → χ''') :
    GraphicVertexFunction (fun (G : Graph α _) ↦ f (A G) (A' G) (A'' G)) (fun (G : Graph α _) ↦ f (A₁ G) (A'₁ G) (A''₁ G)) where
  invariant h := by rw [← hA.invariant h, ← hA'.invariant h, ← hA''.invariant h]

instance instImpGraphicVertex :
  GraphicVertexFunction (fun {β} (G : Graph α β) ↦ P G → Q G) (fun {β} (G : Graph α β) ↦ P₁ G → Q₁ G) :=
  instComp2GraphicVertex (· → ·)

instance instHasIsomLeftGraphicVertex : GraphicVertexFunction |₂ (fun (G : Graph α _) ↦ G ↔ᴳ H) :=
  instGraphicGraphicVertex (hF := instHasIsomLeftGraphic)

instance instHasIsomRightGraphicVertex : GraphicVertexFunction |₂ (fun (G : Graph α _) ↦ H ↔ᴳ G) :=
  instGraphicGraphicVertex (hF := instHasIsomRightGraphic)

instance instHasEmbLeftGraphicVertex : GraphicVertexFunction |₂ (fun (G : Graph α _) ↦ G ↪ᴳ H) :=
  instGraphicGraphicVertex (hF := instHasEmbLeftGraphic)

instance instHasEmbRightGraphicVertex : GraphicVertexFunction |₂ (fun (G : Graph α _) ↦ H ↪ᴳ G) :=
  instGraphicGraphicVertex (hF := instHasEmbRightGraphic)

instance instHasHomLeftGraphicVertex : GraphicVertexFunction |₂ (fun (G : Graph α _) ↦ G →ᴳ H) :=
  instGraphicGraphicVertex (hF := instHasHomLeftGraphic)

instance instHasHomRightGraphicVertex : GraphicVertexFunction |₂ (fun (G : Graph α _) ↦ H →ᴳ G) :=
  instGraphicGraphicVertex (hF := instHasHomRightGraphic)

instance instVxSetGraphicVertex : GraphicVertexFunction |₂ (fun (G : Graph α _) ↦ V(G)) where
  invariant h := by
    obtain ⟨F, hF⟩ := h
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have := congrFun hF ⟨x, hx⟩
      simp only [comp_apply] at this
      rw [← this]
      exact Subtype.coe_prop (F.toFun ⟨x, hx⟩)
    · have : Subtype.val ∘ F.invFun = Subtype.val := by
        ext x
        rw [← hF, comp_apply, comp_apply, F.vx_right_inv]
      have := congrFun this ⟨x, hx⟩
      simp only [comp_apply] at this
      rw [← this]
      exact Subtype.coe_prop (F.invFun ⟨x, hx⟩)

-- instance : GraphicVertexFunction (fun (G : Graph α _) ↦ Finite G.vertexSet → Finite G.vertexSet) (fun (G : Graph α _) ↦ Finite G.vertexSet → Finite G.vertexSet) := inferInstance

instance instEdgeSetFiniteGraphicVertex : GraphicVertexFunction |₂ (fun (G : Graph α _) ↦ Finite E(G)) :=
  instGraphicGraphicVertex (hF := instEdgeSetFiniteGraphic)

instance instEdgeSetNonemptyGraphicVertex : GraphicVertexFunction |₂ (fun (G : Graph α _) ↦ E(G).Nonempty) :=
  instGraphicGraphicVertex (hF := instEdgeSetNonemptyGraphic)

instance instEdgeSetEncardGraphicVertex : GraphicVertexFunction |₂ (fun (G : Graph α _) ↦ E(G).encard) :=
  instGraphicGraphicVertex (hF := instEdgeSetEncardGraphic)

instance instEdgeSetNcardGraphicVertex : GraphicVertexFunction |₂ (fun (G : Graph α _) ↦ E(G).ncard) :=
  instGraphicGraphicVertex (hF := instEdgeSetNcardGraphic)



class GraphicEdgeFunction (f : outParam <| ∀ {α : Type u₀}, Graph α β → χ)
    (g : ∀ {α : Type u₁}, Graph α β → χ) : Prop where
  invariant {α₁ α₂} {G : Graph α₁ β} {G' : Graph α₂ β} :
    (∃ (F : Isom G G'), Subtype.val ∘ F.edgeFun = Subtype.val) → f G = g G'

-- WHY IS THIS NOT WORKING?
instance instGraphicGraphicEdge {β : Type v₀} {f : ∀ {α : Type u₀} {β : Type v₀}, Graph α β → χ}
    {g : ∀ {α : Type u₁} {β : Type v₀}, Graph α β → χ}
    [hF : GraphicFunction f g] : GraphicEdgeFunction (fun G ↦ f (β := β) G) (fun G ↦ g (β := β) G) where
  invariant h := by
    obtain ⟨F, hF⟩ := h
    rw [← HasIsom.eq ⟨F⟩ f g]

example : GraphicEdgeFunction (fun (G : Graph _ β) ↦ E(G).ncard) (fun (G : Graph _ β) ↦ E(G).ncard) :=
  -- inferInstance
  instGraphicGraphicEdge (hF := instEdgeSetNcardGraphic)

variable {A : {α : Type v₀} → (G : Graph α β) → χ}
  {A₁ : {α : Type v₁} → (G : Graph α β) → χ}
  {A' : {α : Type v₀} → (G : Graph α β) → χ'}
  {A'₁ : {α : Type v₁} → (G : Graph α β) → χ'}
  {A'' : {α : Type v₀} → (G : Graph α β) → χ''}
  {A''₁ : {α : Type v₁} → (G : Graph α β) → χ''}
  {P Q : {α : Type v₀} → (G : Graph α β) → Prop}
  {P₁ Q₁ : {α : Type v₁} → (G : Graph α β) → Prop}
  [hA : GraphicEdgeFunction A A₁] [hA' : GraphicEdgeFunction A' A'₁] [hA'' : GraphicEdgeFunction A'' A''₁]
  [hP : GraphicEdgeFunction P P₁] [hQ : GraphicEdgeFunction Q Q₁]

instance instConstGraphicEdge (c : χ) : GraphicEdgeFunction |₂ (fun (_ : Graph _ β) ↦ c) :=
  instGraphicGraphicEdge (hF := instConstGraphic c)

instance instCompGraphicEdge (f : χ' → χ) :
    GraphicEdgeFunction (fun (G : Graph _ β) ↦ f (A' G)) (fun (G : Graph _ β) ↦ f (A'₁ G)) where
  invariant h := by rw [← hA'.invariant h]

instance instComp2GraphicEdge (f : χ → χ' → χ'') :
    GraphicEdgeFunction (fun (G : Graph _ β) ↦ f (A G) (A' G)) (fun (G : Graph _ β) ↦ f (A₁ G) (A'₁ G)) where
  invariant h := by rw [← hA.invariant h, ← hA'.invariant h]

instance instComp3GraphicEdge (f : χ → χ' → χ'' → χ''') :
    GraphicEdgeFunction (fun (G : Graph _ β) ↦ f (A G) (A' G) (A'' G)) (fun (G : Graph _ β) ↦ f (A₁ G) (A'₁ G) (A''₁ G)) where
  invariant h := by rw [← hA.invariant h, ← hA'.invariant h, ← hA''.invariant h]

instance instImpGraphicEdge :
  GraphicEdgeFunction (fun (G : Graph _ β) ↦ P G → Q G) (fun (G : Graph _ β) ↦ P₁ G → Q₁ G) :=
  instComp2GraphicEdge (· → ·)

instance instHasIsomLeftGraphicEdge : GraphicEdgeFunction |₂ (fun (G : Graph _ β) ↦ G ↔ᴳ H) :=
  instGraphicGraphicEdge (hF := instHasIsomLeftGraphic)

instance instHasIsomRightGraphicEdge : GraphicEdgeFunction |₂ (fun (G : Graph _ β) ↦ H ↔ᴳ G) :=
  instGraphicGraphicEdge (hF := instHasIsomRightGraphic)

instance instHasEmbLeftGraphicEdge : GraphicEdgeFunction |₂ (fun (G : Graph _ β) ↦ G ↪ᴳ H) :=
  instGraphicGraphicEdge (hF := instHasEmbLeftGraphic)

instance instHasEmbRightGraphicEdge : GraphicEdgeFunction |₂ (fun (G : Graph _ β) ↦ H ↪ᴳ G) :=
  instGraphicGraphicEdge (hF := instHasEmbRightGraphic)

instance instHasHomLeftGraphicEdge : GraphicEdgeFunction |₂ (fun (G : Graph _ β) ↦ G →ᴳ H) :=
  instGraphicGraphicEdge (hF := instHasHomLeftGraphic)

instance instHasHomRightGraphicEdge : GraphicEdgeFunction |₂ (fun (G : Graph _ β) ↦ H →ᴳ G) :=
  instGraphicGraphicEdge (hF := instHasHomRightGraphic)

instance instEdgeSetGraphicEdge : GraphicEdgeFunction |₂ (fun (G : Graph _ β) ↦ E(G)) where
  invariant h := by
    obtain ⟨F, hF⟩ := h
    ext e
    refine ⟨fun he => ?_, fun he => ?_⟩
    · have := congrFun hF ⟨e, he⟩
      simp only [comp_apply] at this
      rw [← this]
      exact Subtype.coe_prop _
    · have : Subtype.val ∘ F.edgeInvFun = Subtype.val := by
        ext e
        rw [← hF, comp_apply, comp_apply, F.edge_right_inv]
      have := congrFun this ⟨e, he⟩
      simp only [comp_apply] at this
      rw [← this]
      exact Subtype.coe_prop _

instance instVersetSetFiniteGraphicEdge : GraphicEdgeFunction |₂ (fun (G : Graph _ β) ↦ Finite V(G)) :=
  instGraphicGraphicEdge (hF := instVxSetFiniteGraphic)

instance instVertexSetNonemptyGraphicEdge : GraphicEdgeFunction |₂ (fun (G : Graph _ β) ↦ V(G).Nonempty) :=
  instGraphicGraphicEdge (hF := instVxSetNonemptyGraphic)

instance instVertexSetEncardGraphicEdge : GraphicEdgeFunction |₂ (fun (G : Graph _ β) ↦ V(G).encard) :=
  instGraphicGraphicEdge (hF := instVxSetEncardGraphic)

instance instVertexSetNcardGraphicEdge : GraphicEdgeFunction |₂ (fun (G : Graph _ β) ↦ V(G).ncard) :=
  instGraphicGraphicEdge (hF := instVxSetNcardGraphic)


variable {G : Graph α β} {G' : Graph α' β'}

lemma eq_noEdge_of_hasIsom (h : G ↔ᴳ G') :
    G = Graph.noEdge V(G) β ↔ G' = Graph.noEdge V(G') β' :=
  ⟨eq_noEdge_of_Funs h.some.symm.toFuns, eq_noEdge_of_Funs h.some.toFuns⟩

-- lemma hasIsom_iff {G : Graph α β} {G' : Graph α' β'} : G ↔ᴳ G' ↔
--     (Nonempty (V(G) ≃ V(G')) ∧ G = Graph.noEdge V(G) β ∧ G' = Graph.noEdge V(G') β') ∨
--     (∃ (f : α → α') (_ : InjOn f V(G)) (g : β → β') (hg : InjOn g E(G)),
--     G' = (f '' G).edgeMap g (by simpa)) := by
--   refine ⟨fun hisom => ?_, fun h => ?_⟩
--   · let ⟨F⟩ := hisom
--     obtain hβ' | hβ' := isEmpty_or_nonempty β'
--     · have : Nonempty (E(G) → E(G')) := ⟨F.edgeFun⟩
--       left
--       simp only [nonempty_fun, isEmpty_coe_sort, edgeSet_empty_iff_eq_noEdge, nonempty_subtype,
--         IsEmpty.exists_iff, or_false] at this
--       use hisom.vxEquiv, this, eq_noEdge_of_Funs hisom.some.symm.toFuns this

--     obtain hα' | hα' := isEmpty_or_nonempty α'
--     · have : Nonempty (V(G) → V(G')) := ⟨F.toFun⟩
--       left
--       simp only [eq_bot_of_isEmpty, bot_V, nonempty_fun, isEmpty_coe_sort,
--         vertexSet_empty_iff_eq_bot, nonempty_subtype, mem_empty_iff_false, IsEmpty.exists_iff,
--         or_false] at this
--       simp [this]

--     right
--     use (extend Subtype.val (Subtype.val ∘ F.toFun) (Classical.arbitrary _)), ?_,
--       (extend Subtype.val (Subtype.val ∘ F.edgeFun) (Classical.arbitrary _)), ?_
--     apply ext_toMultiset
--     · ext x
--       simp only [edgeMap_vertexSet, vxMap_vertexSet, mem_image]
--       constructor
--       · rintro hx
--         use F.invFun ⟨x, hx⟩, (F.invFun ⟨x, hx⟩).prop, by simp [F.vx_right_inv ⟨x, hx⟩]
--       · rintro ⟨v, hv, rfl⟩
--         have : Subtype.val ⟨v, hv⟩ = v := rfl
--         rw [← this, Subtype.val_injective.extend_apply]
--         simp
--     · rintro e'
--       by_cases he' : e' ∈ E(G')
--       · sorry
--       · simp [he']
--         sorry
--     · rintro a ha b hb heq
--       have haa : a = Subtype.val ⟨a, ha⟩ := rfl
--       have hbb : b = Subtype.val ⟨b, hb⟩ := rfl
--       rwa [haa, hbb, Subtype.val_injective.extend_apply, Subtype.val_injective.extend_apply,
--         (Subtype.val_injective.comp F.inj_vx).eq_iff, Subtype.ext_iff] at heq
--     · rintro e he f hf heq
--       have hee : e = Subtype.val ⟨e, he⟩ := rfl
--       have hff : f = Subtype.val ⟨f, hf⟩ := rfl
--       rwa [hee, hff, Subtype.val_injective.extend_apply, Subtype.val_injective.extend_apply,
--         (Subtype.val_injective.comp F.inj_edge).eq_iff, Subtype.ext_iff] at heq
--   · obtain ⟨⟨F⟩, hG, hG'⟩ | ⟨f, hf, g, hg, rfl⟩ := h
--     · rw [hG, hG', noEdge_hasIsom_noEdge_iff]
--       exact ⟨F⟩
--     · refine (vxMap_hasIsom hf).trans (edgeMap_hasIsom _)
