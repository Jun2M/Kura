import Kura.Graph.Undirected
import Kura.Dep.Finset


namespace Graph
open edge
variable {V W E F : Type*}


def Vp (G : Graph V E) (P : V → Prop) : Graph {v // P v} {e // G.all e P} where
  inc e :=
    let ⟨e, he⟩ := e
    edge.pmap Subtype.mk (G.inc e) (by simpa only [all, all_iff, decide_eq_true_eq] using he)

def Vs (G : Graph V E) (S : Set V) : Graph S {e // G.all e (· ∈ S) } :=
  G.Vp (· ∈ S)

macro G:term "[" S:term "]ᴳ" : term => `(Graph.Vs $G $S)

def VpSubtype {Pᵥ Pᵥ' : V → Prop} {Pₑ Pₑ' : E → Prop} (G : Graph (Subtype Pᵥ) (Subtype Pₑ))
    (S : Set V) (hPᵥ' : ∀ v, (Pᵥ v ∧ v ∈ S) ↔ Pᵥ' v)
    (hPₑ' : ∀ e, (∃ (he : Pₑ e), G.all ⟨e, he⟩ (·.val ∈ S)) ↔ Pₑ' e):
    Graph (Subtype Pᵥ') (Subtype Pₑ') where
  inc e := by
    choose he' hS using (hPₑ' e).mpr e.prop
    apply edge.pmap Subtype.mk ((G.inc ⟨e.val, he'⟩).map Subtype.val)
    simp only [all, all_iff, decide_eq_true_eq, Subtype.forall, mem_map_iff, Subtype.exists,
      exists_and_right, exists_eq_right, forall_exists_index] at hS ⊢
    rintro v hv hvG
    rw [← hPᵥ']
    refine ⟨hv, hS v hv hvG⟩

def Ep (G : Graph V E) (P : E → Prop) : Graph V {e // P e} where
  inc := (G.inc ·.val)

def Es (G : Graph V E) (S : Set E) : Graph V S := G.Ep (· ∈ S)

macro G:term "{" S:term "}ᴳ" : term => `(Graph.Es $G $S)

def EsSubtype {P P' : E → Prop} (G : Graph V (Subtype P)) (S : Set E)
  (hP' : ∀ e, (P e ∧ e ∈ S) ↔ P' e) : Graph V (Subtype P') where
  inc e := by
    obtain ⟨e, he⟩ := e
    specialize hP' e
    rw [← hP'] at he; clear hP'
    obtain ⟨hP, _hS⟩ := he
    exact G.inc ⟨e, hP⟩

/-subgraph creator-/
def EVSubgraph (G : Graph V E) (Sv : Set V) (Se : Set E) (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) :
    Graph Sv Se where
  inc e := G{Se}ᴳ[Sv]ᴳ.inc ⟨e, he e.val e.prop⟩

-- def VESubgraph (G : Graph V E) (Sv : Set V) (Se : Set E) (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) :
--     Graph Sv Se where
--   inc e :=
--     let Se' : Set { e // G.all e fun x ↦ x ∈ Sv } :=
--       Subtype.map id (fun f (hSf : f ∈ Se) => he (id f) hSf) ''
--     G[Sv]ᴳ{Se'}ᴳ.inc ⟨e, he e.val e.prop⟩

-- def Subgraph (G : Graph V E) (Sv : Set V) (Se : Set E) (he : ∀ e ∈ Se, ∀ v ∈ G.inc e, v ∈ Sv) :
--     Graph Sv Se where
--   inc e := edge.pmap Subtype.mk (G.inc e) (he e.val e.prop)

def Qs (G : Graph V E) (S : Set V) [DecidablePred (· ∈ S)] (v : V) (hv : v ∉ S) :
  Graph (Sᶜ:Set _) E where
  inc e := G.inc e
    |>.map (fun u => if u ∈ S then v else u)
    |>.pmap Subtype.mk (fun w hw => by
      simp only [mem_map_iff] at hw
      obtain ⟨u, _hu, rfl⟩ := hw
      split
      · exact hv
      · assumption)

def Qf (G : Graph V E) (f : V → V) (_ : ∀ v, f (f v) = f v) : Graph (Set.range f) E where
  inc e := G.inc e
    |>.map f
    |>.pmap Subtype.mk (fun v hv => by
      simp only [mem_map_iff] at hv
      obtain ⟨u, _hu, rfl⟩ := hv
      simp only [Set.mem_range, exists_apply_eq_apply])

def Qfp (G : Graph V E) (f : V → V) {P : V → Prop} (_ : ∀ v, f (f v) = f v)
  (hfRange : ∀ v, v ∈ Set.range f ↔ P v) : Graph (Subtype P) E where
  inc e := G.inc e
    |>.map f
    |>.pmap Subtype.mk (fun v hv => by
      simp only [mem_map_iff] at hv
      obtain ⟨u, _hu, rfl⟩ := hv
      specialize hfRange (f u)
      simpa only [Set.mem_range, exists_apply_eq_apply, true_iff] using hfRange)

--------------------------------------------------------------------------------
variable (G : Graph V E) {S T : Set V}

def Vs_univ : (G[Set.univ]ᴳ) ≃ᴳ G where
  fᵥ := Subtype.val
  fₑ := Subtype.val
  inc e := by simp only [all, Vs, Vp, pmap_subtype_map_val]
  fᵥinj := Subtype.val_injective
  fₑinj := Subtype.val_injective
  fᵥsurj v := by simp only [Subtype.exists, Set.mem_univ, exists_const, exists_eq]
  fₑsurj e := by simp only [all, Subtype.exists, Set.mem_univ, decide_true, all_iff, implies_true,
    exists_const, exists_eq]

@[simp]
lemma Vs_univ_fᵥ : (G.Vs_univ).fᵥ = Subtype.val := rfl

@[simp]
lemma Vs_univ_fₑ : (G.Vs_univ).fₑ = Subtype.val := rfl

@[simp]
lemma Vs_univ_fᵥEquiv : (G.Vs_univ).fᵥEquiv = Equiv.Set.univ V := Equiv.ext (fun _ => rfl)

@[simp]
lemma Vs_univ_fₑEquiv : (G.Vs_univ).fₑEquiv = Equiv.subtypeUnivEquiv (fun e => by simp) :=
  Equiv.ext (fun _ => rfl)


def Vs_congr (h : S = T) : G[S]ᴳ ≃ᴳ G[T]ᴳ where
  fᵥ v := ⟨v.val, h ▸ v.prop⟩
  fₑ e := ⟨e.val, by
    have he := e.prop; simp only [all, all_iff, decide_eq_true_eq] at he ⊢;
    exact fun v hv => h ▸ (he v hv)⟩
  inc e := by
    obtain ⟨e, he⟩ := e
    simp only [all, all_iff, decide_eq_true_eq, Vs, Vp] at he ⊢
    rw [map_pmap]
    simp only
    apply pmap_congr
    intro v hv
    rfl
  fᵥinj u v hv := by simp only [Subtype.mk.injEq] at hv; exact SetCoe.ext hv
  fₑinj e1 e2 he := by simp only [all, Subtype.mk.injEq] at he; exact Subtype.eq he
  fᵥsurj v := by simp only [Subtype.exists]; use v.val, h ▸ v.prop
  fₑsurj e := by simp only [all, Subtype.exists, h, all_iff]; use e.val, (by
    obtain ⟨e, he⟩ := e
    simp only [all, ← h, all_iff, decide_eq_true_eq] at he ⊢
    exact he)

@[simp]
lemma Vs_congr_fᵥ (h : S = T) : (G.Vs_congr h).fᵥ = fun v => ⟨v.val, h ▸ v.prop⟩ := rfl

@[simp]
lemma Vs_congr_fₑ (h : S = T) : (G.Vs_congr h).fₑ = fun e => ⟨e.val, by
  have he := e.prop; simp only [all, all_iff, decide_eq_true_eq] at he ⊢;
  exact fun v hv => h ▸ (he v hv)⟩ := rfl

@[simp]
lemma Vs_congr_fᵥEquiv (h : S = T) : (G.Vs_congr h).fᵥEquiv = Equiv.setCongr h :=
  Equiv.ext (fun _ => rfl)

@[simp]
lemma Vs_congr_fₑEquiv (h : S = T) : (G.Vs_congr h).fₑEquiv = Equiv.subtypeEquivProp (h ▸ rfl) :=
  Equiv.ext (fun _ => rfl)

@[simp]
lemma SubtypeVal_Vs_congr_fₑ (h : S = T) : Subtype.val ∘ (G.Vs_congr h).fₑ = Subtype.val := rfl

@[simp]
def Vs_empty_compl (G : Graph V E) : G[∅ᶜ]ᴳ ≃ᴳ G :=
  (G.Vs_congr Set.compl_empty).trans (G.Vs_univ)

def Vs_subgraph (G : Graph V E) (S : Set V) : G[S]ᴳ ⊆ᴳ G where
  fᵥ := (·.val)
  fₑ := (·.val)
  inc e := by simp only [all, Vs, Vp, pmap_subtype_map_val]
  fᵥinj := Subtype.val_injective
  fₑinj := Subtype.val_injective

@[simp]
lemma Vs_inc (G : Graph V E) (S : Set V) (e : {e // G.all e (· ∈ S)}) :
    ((G[S]ᴳ).inc e).map Subtype.val = G.inc e.val := ((Vs_subgraph G S).inc e).symm

@[simp]
lemma Vs_subgraph_fᵥ {G : Graph V E} (S : Set V) :
    (Vs_subgraph G S).fᵥ = Subtype.val := rfl

@[simp]
lemma Vs_subgraph_fₑ {G : Graph V E} (S : Set V) :
    (Vs_subgraph G S).fₑ = Subtype.val := rfl

def Vs_EmbSpanningEmb_Vs_of_subset (h : S ⊆ T) : G[S]ᴳ ⊆ᴳ G[T]ᴳ where
  fᵥ v := ⟨v.val, h v.prop⟩
  fₑ e := ⟨e.val, by
    have he := e.prop; simp only [all, all_iff, decide_eq_true_eq] at he ⊢; exact (h <| he · ·)⟩
  inc e := by
    obtain ⟨e, he⟩ := e
    simp only [all, all_iff, decide_eq_true_eq, Vs, Vp] at he ⊢
    rw [map_pmap]
    simp only
    apply pmap_congr
    intro v hv
    rfl
  fᵥinj v w hv := by
    simp only [Subtype.mk.injEq] at hv
    exact Subtype.eq hv
  fₑinj e1 e2 he := by
    simp only [all, Subtype.mk.injEq] at he
    exact Subtype.eq he

@[simp]
lemma Es_inc (G : Graph V E) (S : Set E) (e : S) :
    (G{S}ᴳ).inc e = G.inc e := rfl

instance instEsUndir [Undirected G] {S : Set E} : G{S}ᴳ.Undirected where
  all_full e := by
    obtain ⟨e, he⟩ := e
    exact G.all_full e
  edge_symm e := by
    obtain ⟨e, he⟩ := e
    exact G.edge_symm e

instance instEsSimple [Simple G] {S : Set E} : G{S}ᴳ.Simple where
  edge_symm e := by
    obtain ⟨e, he⟩ := e
    exact G.edge_symm e
  all_full e := by
    obtain ⟨e, he⟩ := e
    exact G.all_full e
  no_loops e := by
    obtain ⟨e, he⟩ := e
    exact G.no_loops e
  inc_inj e₁ e₂ h := by
    obtain ⟨e₁, he₁⟩ := e₁
    obtain ⟨e₂, he₂⟩ := e₂
    ext
    exact G.inc_inj h

def Es_univ : (G{Set.univ}ᴳ) ≃ᴳ G where
  fᵥ := id
  fₑ := Subtype.val
  inc e := by simp only [Es, Ep, map_id]
  fᵥinj := Function.injective_id
  fₑinj := Subtype.val_injective
  fᵥsurj v := by simp only [id_eq, exists_eq]
  fₑsurj e := by simp only [Subtype.exists, Set.mem_univ, exists_const, exists_eq]

@[simp]
lemma Es_univ_fᵥ : (G.Es_univ).fᵥ = id := rfl

@[simp]
lemma Es_univ_fᵥEquiv {G : Graph V E} : (G.Es_univ).fᵥEquiv = Equiv.refl _ :=
  Equiv.ext (fun _ => rfl)


@[simp]
lemma Es_univ_fₑ : (G.Es_univ).fₑ = Subtype.val := rfl

def Es_congr {S T : Set E} (h : S = T) : G{S}ᴳ ≃ᴳ G{T}ᴳ where
  fᵥ := id
  fₑ e := ⟨e.val, h ▸ e.prop⟩
  inc e := by simp only [Es, Ep, map_id]
  fᵥinj := Function.injective_id
  fₑinj e1 e2 he := by simp only [Subtype.mk.injEq] at he; exact Subtype.eq he
  fᵥsurj := Function.surjective_id
  fₑsurj e := by simp only [Subtype.exists, h, exists_subtype_mk_eq_iff, exists_eq]

@[simp]
lemma Es_congr_fᵥ {S T : Set E} (h : S = T) : (G.Es_congr h).fᵥ = id := rfl

@[simp]
lemma Es_congr_fᵥEquiv {S T : Set E} (h : S = T) : (G.Es_congr h).fᵥEquiv = Equiv.refl _ :=
  Equiv.ext (fun _ => rfl)

@[simp]
lemma Es_congr_fₑ {S T : Set E} (h : S = T) :
    (G.Es_congr h).fₑ = Equiv.subtypeEquivProp (h ▸ rfl) := by
  ext e; rfl

@[simp]
lemma Es_congr_fₑEquiv {S T : Set E} (h : S = T) :
    (G.Es_congr h).fₑEquiv = Equiv.subtypeEquivProp (h ▸ rfl) := by
  ext e; rfl

@[simp]
lemma SubtypeVal_Es_congr_fₑ {S T : Set E} (h : S = T) :
    Subtype.val ∘ (G.Es_congr h).fₑ = Subtype.val := rfl

@[simp]
def Es_empty_compl (G : Graph V E) : G{∅ᶜ}ᴳ ≃ᴳ G :=
  (G.Es_congr Set.compl_empty).trans (G.Es_univ)

def Es_spanningsubgraph (G : Graph V E) (S : Set E) : G{S}ᴳ.SpanningEmb G where
  fᵥ := id
  fₑ := Subtype.val
  inc := by simp only [Es_inc, map_id, implies_true]
  fᵥinj := Function.injective_id
  fᵥsurj := Function.surjective_id
  fₑinj := Subtype.val_injective

@[simp]
lemma Es_spanningsubgraph_fᵥ (S : Set E) : (Es_spanningsubgraph G S).fᵥ = id := rfl

@[simp]
lemma Es_spanningsubgraph_fₑ (S : Set E) : (Es_spanningsubgraph G S).fₑ = Subtype.val := rfl

def Es_spanningsubgraph_Es_of_subset {S T : Set E} (h : S ⊆ T) :
  G{S}ᴳ.SpanningEmb (G{T}ᴳ) where
  fᵥ := id
  fₑ := Subtype.impEmbedding _ _ h
  inc e := by simp only [Es_inc, Subtype.impEmbedding_apply_coe, map_id]
  fᵥinj := Function.injective_id
  fᵥsurj := Function.surjective_id
  fₑinj e1 e2 he := by simpa only [EmbeddingLike.apply_eq_iff_eq] using he

@[simp]
lemma Es_spanningsubgraph_Es_of_subset_fᵥ {S T : Set E} (h : S ⊆ T) :
    (G.Es_spanningsubgraph_Es_of_subset h).fᵥ = id := rfl

@[simp]
lemma Es_spanningsubgraph_Es_of_subset_fₑ {S T : Set E} (h : S ⊆ T) :
    (G.Es_spanningsubgraph_Es_of_subset h).fₑ = Subtype.impEmbedding _ _ h := rfl

def Es_of_Es_Es (S : Set E) (T : Set S) {U : Set E} (hU : U = Subtype.val '' T) :
    G{U}ᴳ ≃ᴳ G{S}ᴳ{T}ᴳ where
  fᵥ := id
  fₑ e : T.Elem := ⟨⟨e.val, (by
    subst U
    obtain ⟨e, ⟨⟨a, haS⟩, haT, rfl⟩⟩ := e
    exact haS)⟩, (by
    subst U
    obtain ⟨e, ⟨⟨a, haS⟩, haT, rfl⟩⟩ := e
    exact haT)⟩
  inc := by simp only [Es_inc, map_id, implies_true]
  fᵥinj := Function.injective_id
  fₑinj e f hef := by
    ext
    simpa only [Subtype.mk.injEq] using hef
  fᵥsurj := Function.surjective_id
  fₑsurj e := by
    subst U
    simp only [Subtype.exists, Set.mem_image, exists_and_right, exists_eq_right]
    obtain ⟨⟨e, heS⟩, heT⟩ := e
    use e, ⟨heS, heT⟩


@[simp]
lemma Es_of_Es_Es_fᵥ (S : Set E) (T : Set S) {U : Set E} (hU : U = Subtype.val '' T) :
    (G.Es_of_Es_Es S T hU).fᵥ = id := rfl

-- @[simp]
-- lemma Es_of_Es_Es_fₑ {S : Set E} (T : Set S) {U : Set E} (hU : U = Subtype.val '' T) :
--     (G.Es_of_Es_Es S T hU).fₑ = (Equiv.setCongr hU) ∘ sorry := rfl

@[simp]
lemma Es_of_Es_Es_symm_fᵥ (S : Set E) (T : Set S) {U : Set E} (hU : U = Subtype.val '' T) :
    (G.Es_of_Es_Es S T hU).symm.fᵥ = id := by
  ext v
  apply_fun (G.Es_of_Es_Es S T hU).fᵥ using (G.Es_of_Es_Es S T hU).fᵥinj
  simp only [Isom.fᵥ_symm_fᵥ, id_eq, Es_of_Es_Es_fᵥ]

-- @[simp]
-- lemma Es_of_Es_Es_symm_fₑ {S : Set E} (T : Set S) :
--     (G.Es_of_Es_Es T).symm.fₑ = Subtype.impEmbedding _ _ (fun _ he => he) := rfl

@[simp]
lemma Es_get {G : Graph V E} [Undirected G] (S : Set E) (e : S) : (G{S}ᴳ).get e = G.get e := rfl

def Hom.Es {G : Graph V E} {H : Graph W F} (σ : G.Hom H) (S : Set F) (hσ : ∀ e, σ.fₑ e ∈ S) :
    G.Hom (H{S}ᴳ) where
  fᵥ := σ.fᵥ
  fₑ e := ⟨σ.fₑ e, hσ e⟩
  inc e := σ.inc e

@[simp]
lemma Hom.Es_fᵥ {G : Graph V E} {H : Graph W F} (σ : G.Hom H) (S : Set F) (hσ : ∀ e, σ.fₑ e ∈ S) :
    (σ.Es S hσ).fᵥ = σ.fᵥ := rfl

@[simp]
lemma Hom.Es_fₑ {G : Graph V E} {H : Graph W F} (σ : G.Hom H) (S : Set F) (hσ : ∀ e, σ.fₑ e ∈ S) :
    (σ.Es S hσ).fₑ = fun e => ⟨σ.fₑ e, hσ e⟩ := rfl

def Emb.Es {G : Graph V E} {H : Graph W F} (σ : G ⊆ᴳ H) (S : Set F) (hσ : ∀ e, σ.fₑ e ∈ S) :
    G ⊆ᴳ H{S}ᴳ where
  toHom := σ.toHom.Es S hσ
  fᵥinj := σ.fᵥinj
  fₑinj a b h := by
    simp only [Hom.Es, Subtype.mk.injEq] at h
    exact σ.fₑinj h

def SpanningEmb.Es {G : Graph V E} {H : Graph W F} (σ : G.SpanningEmb H) (S : Set F)
    (hσ : ∀ e, σ.fₑ e ∈ S) : G.SpanningEmb (H{S}ᴳ) where
  toEmb := σ.toEmb.Es S hσ
  fᵥsurj := σ.fᵥsurj

def Emb.Es_Es {G : Graph V E} {H : Graph W F} (σ : G ⊆ᴳ H) (S : Set E) (T : Set F)
    (hσ : σ.fₑ '' S ⊆ T) : G{S}ᴳ ⊆ᴳ H{T}ᴳ where
  fᵥ := σ.fᵥ
  fₑ e := ⟨σ.fₑ e.val, hσ (Set.mem_image_of_mem _ e.prop)⟩
  inc e := by simp only [Es_inc, σ.inc]
  fᵥinj := σ.fᵥinj
  fₑinj a b h := by
    ext
    simpa [Subtype.mk.injEq, σ.fₑinj.eq_iff] using h

@[simp]
lemma Emb.Es_Es_fᵥ {G : Graph V E} {H : Graph W F} (σ : G ⊆ᴳ H) (S : Set E) (T : Set F)
    (hσ : σ.fₑ '' S ⊆ T) : (σ.Es_Es S T hσ).fᵥ = σ.fᵥ := rfl

@[simp]
lemma Emb.Es_Es_fₑ {G : Graph V E} {H : Graph W F} (σ : G ⊆ᴳ H) (S : Set E) (T : Set F)
    (hσ : σ.fₑ '' S ⊆ T) : (σ.Es_Es S T hσ).fₑ =
    fun e => ⟨σ.fₑ e.val, hσ (Set.mem_image_of_mem _ e.prop)⟩ := rfl

def Isom.Es_Es {G : Graph V E} {H : Graph W F} (σ : G ≃ᴳ H) {S : Set E} {T : Set F}
    (hσ : σ.fₑ '' S = T) : G{S}ᴳ ≃ᴳ H{T}ᴳ where
  fᵥ := σ.fᵥ
  fₑ e := ⟨σ.fₑ e.val, by simp only [←hσ, Set.mem_image, σ.fₑinj.eq_iff, exists_eq_right, e.prop]⟩
  inc e := by simp only [Es_inc, σ.inc]
  fᵥinj := σ.fᵥinj
  fₑinj a b h := by
    ext
    simpa [Subtype.mk.injEq, σ.fₑinj.eq_iff] using h
  fᵥsurj := σ.fᵥsurj
  fₑsurj e := by
    subst T
    obtain ⟨e, ⟨a, ha, rfl⟩⟩ := e
    simp only [Subtype.mk.injEq, σ.fₑinj.eq_iff, Subtype.exists, exists_prop, exists_eq_right, ha]

@[simp]
lemma Isom.Es_Es_fᵥ {G : Graph V E} {H : Graph W F} (σ : G ≃ᴳ H) {S : Set E} {T : Set F}
    (hσ : σ.fₑ '' S = T) : (σ.Es_Es hσ).fᵥ = σ.fᵥ := rfl

@[simp]
lemma Isom.Es_Es_fₑ {G : Graph V E} {H : Graph W F} (σ : G ≃ᴳ H) {S : Set E} {T : Set F}
    (hσ : σ.fₑ '' S = T) : (σ.Es_Es hσ).fₑ = fun e => ⟨σ.fₑ e.val, by
    simp only [←hσ, Set.mem_image, σ.fₑinj.eq_iff, exists_eq_right, e.prop]⟩ := rfl

@[simp]
lemma Isom.Es_Es_symm_fᵥ {G : Graph V E} {H : Graph W F} (σ : G ≃ᴳ H) {S : Set E} {T : Set F}
    (hσ : σ.fₑ '' S = T) : (σ.Es_Es hσ).symm.fᵥ = σ.symm.fᵥ := by
  ext1 v
  apply_fun (σ.Es_Es hσ).fᵥ using σ.fᵥinj
  simp only [fᵥ_symm_fᵥ, Es_Es_fᵥ]

@[simp]
lemma Isom.Es_Es_symm_fₑ {G : Graph V E} {H : Graph W F} (σ : G ≃ᴳ H) {S : Set E} {T : Set F}
    (hσ : σ.fₑ '' S = T) : (σ.Es_Es hσ).symm.fₑ = fun e => ⟨σ.symm.fₑ e.val, by
    obtain ⟨e, he⟩ := e
    obtain ⟨e, he, rfl⟩ := hσ ▸ he
    simpa⟩ := by
  ext1 e
  apply_fun (σ.Es_Es hσ).fₑ using (σ.Es_Es hσ).fₑinj
  simp only [fₑ_symm_fₑ, Es_Es_fₑ]



@[simp]
lemma EVSubgraph_inc (Sv : Set V) (Se : Set E) (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) (e : Se) :
    (G.EVSubgraph Sv Se he).inc e = (G.inc e).pmap Subtype.mk (by
      specialize he e.val e.prop; simpa only [all, all_iff, decide_eq_true_eq] using he) := rfl

def EVSubgraphSpanningEmb (G : Graph V E) (Sv : Set V) (Se : Set E) (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) :
    G.EVSubgraph Sv Se he ⊆ᴳ G where
  fᵥ := Subtype.val
  fₑ := Subtype.val
  inc e := by simp only [Function.Embedding.coeFn_mk, EVSubgraph_inc, pmap_subtype_map_val]
  fᵥinj := Subtype.val_injective
  fₑinj := Subtype.val_injective

@[simp]
lemma EVSubgraphSpanningEmb_fᵥ (Sv : Set V) (Se : Set E) (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) :
    (EVSubgraphSpanningEmb G Sv Se he).fᵥ = Subtype.val := rfl

@[simp]
lemma EVEmbSpanningEmb_fₑ (Sv : Set V) (Se : Set E) (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) :
    (EVSubgraphSpanningEmb G Sv Se he).fₑ = Subtype.val := rfl


lemma subgraph_iff_isom_EVs (G : Graph V E) (H : Graph W F) [Fintype V] [Fintype W] [Fintype E]
  [Fintype F] [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F] :
    Nonempty (G ⊆ᴳ H) ↔ ∃ (Sv : Set W) (Se : Set F) (hSve : ∀ e ∈ Se, (H.all e (· ∈ Sv))),
    Nonempty (G ≃ᴳ H.EVSubgraph Sv Se hSve) := by
  constructor
  · rintro ⟨⟨⟨fᵥ, fₑ, hcomm⟩, fᵥinj, fₑinj⟩⟩
    refine ⟨ Set.range fᵥ, Set.range fₑ, ?_, ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩⟩ ⟩
    · intro e he
      simp only [Set.mem_range, all, all_iff, decide_eq_true_eq] at he ⊢
      intro w hw
      obtain ⟨e, he, rfl⟩ := he
      rw [hcomm e, mem_map_iff] at hw
      obtain ⟨v, _hv, rfl⟩ := hw
      use v
    · exact (Function.Embedding.rangeFactorization ⟨fᵥ, fᵥinj⟩).toFun
    · exact (Function.Embedding.rangeFactorization ⟨fₑ, fₑinj⟩).toFun
    · intro e
      simp only [Function.Embedding.coeFn_mk, Function.Embedding.toFun_eq_coe, EVSubgraph_inc]
      change pmap _ (H.inc (fₑ e)) _ = _
      simp_rw [hcomm e]
      rw [pmap_map (by simp only [Set.mem_range, exists_apply_eq_apply, implies_true])]
      match G.inc e with
      | dir (a, b) => cases a <;> cases b <;> simp <;> aesop
      | undir s =>
        induction' s with x y
        simp_all only [pmap_undir, map_undir, Sym2.map_pair_eq, undir.injEq]
        rfl
    · exact (Function.Embedding.rangeFactorization ⟨fᵥ, fᵥinj⟩).inj'
    · exact (Function.Embedding.rangeFactorization ⟨fₑ, fₑinj⟩).inj'
    · rintro ⟨e, ⟨e, rfl⟩⟩
      simp only [Function.Embedding.coeFn_mk, Function.Embedding.toFun_eq_coe]
      use e
      rfl
    · rintro ⟨e, ⟨e, rfl⟩⟩
      simp only [Function.Embedding.coeFn_mk, Function.Embedding.toFun_eq_coe]
      use e
      rfl
  · rintro ⟨Sv, Se, hall, ⟨hIsom⟩⟩
    refine ⟨⟨⟨(hIsom.fᵥ ·), (hIsom.fₑ ·), ?_⟩, ?_, ?_⟩⟩
    · intro e
      have := hIsom.inc e
      simp only [EVSubgraph_inc] at this
      apply_fun (edge.map Subtype.val) at this
      simp only [pmap_subtype_map_val] at this
      rw [this, ← map_comp]
      rfl
    · simp only
      intro a b h
      apply hIsom.fᵥinj
      simp only at h
      exact SetCoe.ext h
    · simp only
      intro a b h
      apply hIsom.fₑinj
      simp only at h
      exact Subtype.eq h

@[simp]
lemma Qs_inc (G : Graph V E) (S : Set V) [DecidablePred (· ∈ S)] (v : V) (hv : v ∉ S) (e : E) :
    ((G.Qs S v hv).inc e).map Subtype.val = (G.inc e).map (fun u => if u ∈ S then v else u) := by
  simp only [Qs, pmap_subtype_map_val]


end Graph
