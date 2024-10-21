import Kura.Graph.Undirected
import Kura.Dep.Finset


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W]



def Vs (G : Graph V E) (S : Set V) [DecidablePred (· ∈ S)] : Graph S {e // G.all e (· ∈ S) } where
  inc e :=
    let ⟨e, he⟩ := e
    edge.pmap Subtype.mk (G.inc e) (by
    intro v hv
    simp only [all, all_iff, decide_eq_true_eq] at he
    exact he v hv)

macro G:term "[" S:term "]ᴳ" : term => `(Graph.Vs $G $S)

def Vsp (G : Graph V E) (S : Set V) [DecidablePred (· ∈ S)] {P : E → Prop}
  (hP : ∀ e, G.all e (· ∈ S) ↔ P e) : Graph S {e // P e} where
  inc e := G.inc e.val
    |>.pmap Subtype.mk (fun v hv => by
      obtain ⟨e, he⟩ := e
      simp only [← hP e, all, all_iff, decide_eq_true_eq] at he
      exact he v hv)

def Es (G : Graph V E) (S : Set E) [DecidablePred (· ∈ S)] : Graph V S where
  inc := (G.inc ·.val)

macro G:term "{" S:term "}ᴳ" : term => `(Graph.Es $G $S)

def EsSubtype {P P' : E → Prop} (G : Graph V (Subtype P)) (S : Set E) [DecidablePred (· ∈ S)]
  (hP' : ∀ e, (P e ∧ e ∈ S) ↔ P' e) : Graph V (Subtype P') where
  inc e := by
    obtain ⟨e, he⟩ := e
    specialize hP' e
    rw [← hP'] at he; clear hP'
    obtain ⟨hP, _hS⟩ := he
    exact G.inc ⟨e, hP⟩

def EVs (G : Graph V E) (Sv : Set V) [DecidablePred (· ∈ Sv)] (Se : Set E)
  [DecidablePred (· ∈ Se)] (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) : Graph Sv Se where
  inc e := G{Se}ᴳ[Sv]ᴳ.inc ⟨e, he e.val e.prop⟩

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

def Qf (G : Graph V E) (f : V → V) (hf : ∀ v, f (f v) = f v) : Graph (Set.range f) E where
  inc e := G.inc e
    |>.map f
    |>.pmap Subtype.mk (fun v hv => by
      simp only [mem_map_iff] at hv
      obtain ⟨u, _hu, rfl⟩ := hv
      simp only [Set.mem_range, exists_apply_eq_apply])

def Qfp (G : Graph V E) (f : V → V) {P : V → Prop} (hf : ∀ v, f (f v) = f v)
  (hfRange : ∀ v, v ∈ Set.range f ↔ P v) : Graph (Subtype P) E where
  inc e := G.inc e
    |>.map f
    |>.pmap Subtype.mk (fun v hv => by
      simp only [mem_map_iff] at hv
      obtain ⟨u, _hu, rfl⟩ := hv
      specialize hfRange (f u)
      simpa only [Set.mem_range, exists_apply_eq_apply, true_iff] using hfRange)


--------------------------------------------------------------------------------
@[simp]
lemma Vs_inc (G : Graph V E) (S : Set V) [DecidablePred (· ∈ S)] (e : {e // G.all e (· ∈ S)}) :
    ((G[S]ᴳ).inc e).map (Subtype.val) = G.inc e.val := by
  sorry

def Vs_subgraph (G : Graph V E) (S : Set V) [DecidablePred (· ∈ S)] : G[S]ᴳ ⊆ᴳ G where
  fᵥ := { toFun := (·.val), inj' := fun e₁ e₂ h => SetCoe.ext h }
  fₑ := { toFun := (·.val), inj' := fun e₁ e₂ h => SetCoe.ext h }
  comm := by
    rintro ⟨e, he⟩
    simp only [all, Function.Embedding.coeFn_mk, Vs_inc]

@[simp]
lemma Vs_subgraph_fᵥ {G : Graph V E} (S : Set V) [DecidablePred (· ∈ S)] :
    (Vs_subgraph G S).fᵥ.toFun = Subtype.val := rfl

@[simp]
lemma Vs_subgraph_fₑ {G : Graph V E} (S : Set V) [DecidablePred (· ∈ S)] :
    (Vs_subgraph G S).fₑ.toFun = Subtype.val := rfl


@[simp]
lemma Es_inc (G : Graph V E) (S : Set E) [DecidablePred (· ∈ S)] (e : S) :
    (G{S}ᴳ).inc e = G.inc e := by rfl

def Es_subgraph (G : Graph V E) (S : Set E) [DecidablePred (· ∈ S)] : G{S}ᴳ ⊆ᴳ G where
  fᵥ := { toFun := id, inj' := fun e₁ e₂ h => h }
  fₑ := { toFun := Subtype.val, inj' := fun e₁ e₂ h => SetCoe.ext h }
  comm := by
    rintro ⟨e, _he⟩
    simp only [Function.Embedding.coeFn_mk, Es_inc, map_id]

@[simp]
lemma Es_subgraph_fᵥ {G : Graph V E} (S : Set E) [DecidablePred (· ∈ S)] :
    ⇑(Es_subgraph G S).fᵥ = id := rfl

@[simp]
lemma Es_subgraph_fₑ {G : Graph V E} (S : Set E) [DecidablePred (· ∈ S)] :
    ⇑(Es_subgraph G S).fₑ = Subtype.val := rfl


@[simp]
lemma EVs_inc (G : Graph V E) (Sv : Set V) [DecidablePred (· ∈ Sv)] (Se : Set E)
  [DecidablePred (· ∈ Se)] (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) (e : Se) :
    (G.EVs Sv Se he).inc e = (G.inc e).pmap Subtype.mk (by
      specialize he e.val e.prop; simpa only [all, all_iff, decide_eq_true_eq] using he) := by rfl

def EVs_subgraph (G : Graph V E) (Sv : Set V) [DecidablePred (· ∈ Sv)] (Se : Set E)
  [DecidablePred (· ∈ Se)] (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) : G.EVs Sv Se he ⊆ᴳ G where
  fᵥ := { toFun := Subtype.val, inj' := fun e₁ e₂ h => SetCoe.ext h }
  fₑ := { toFun := Subtype.val, inj' := fun e₁ e₂ h => SetCoe.ext h }
  comm := by
    rintro ⟨e, he⟩
    simp only [Function.Embedding.coeFn_mk, EVs_inc, pmap_subtype_map_val]

@[simp]
lemma EVs_subgraph_fᵥ {G : Graph V E} (Sv : Set V) [DecidablePred (· ∈ Sv)] (Se : Set E)
  [DecidablePred (· ∈ Se)] (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) :
    (EVs_subgraph G Sv Se he).fᵥ.toFun = Subtype.val := rfl

@[simp]
lemma EVs_subgraph_fₑ {G : Graph V E} (Sv : Set V) [DecidablePred (· ∈ Sv)] (Se : Set E)
  [DecidablePred (· ∈ Se)] (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) :
    (EVs_subgraph G Sv Se he).fₑ.toFun = Subtype.val := rfl


lemma subgraph_iff_isom_EVs (G : Graph V E) (H : Graph W F) [Fintype V] [Fintype W] [Fintype E]
  [Fintype F] [DecidableEq E] [DecidableEq F] :
    Nonempty (G ⊆ᴳ H) ↔ ∃ (Sv : Set W) (hSv : DecidablePred (· ∈ Sv)) (Se : Set F)
    (hSe : DecidablePred (· ∈ Se)) (hSve : ∀ e ∈ Se, (H.all e (· ∈ Sv))),
    Nonempty (G ≃ᴳ H.EVs Sv Se hSve) := by
  constructor
  · rintro ⟨⟨fᵥ, fₑ, hcomm⟩⟩
    refine ⟨ Set.range fᵥ, by infer_instance, Set.range fₑ, by infer_instance, ?_, ⟨⟨?_, ?_⟩⟩ ⟩
    · intro e he
      simp only [Set.mem_range, all, all_iff, decide_eq_true_eq] at he ⊢
      intro w hw
      obtain ⟨e, he, rfl⟩ := he
      rw [hcomm e, mem_map_iff] at hw
      obtain ⟨v, _hv, rfl⟩ := hw
      use v
    · refine ⟨fᵥ.rangeFactorization, fₑ.rangeFactorization, ?_⟩
      intro e
      rw [EVs_inc]
      simp only [Function.Embedding.rangeFactorization_apply]
      have : (Multiset.map (↑·: { x // x ∈ Set.range ⇑fᵥ } → W)).Injective :=
        Multiset.map_injective Subtype.val_injective
      ext1 <;> simp only [Function.Embedding.rangeSplitting_apply, map_startAt, pmap_startAt,
        map_finishAt, pmap_finishAt] <;> apply_fun (Multiset.map Subtype.val) using this <;>
      simp only [hcomm e, Function.Embedding.rangeFactorization_apply, ← map_startAt,
        ← map_finishAt] <;> clear this <;>
      change Multiset.map Subtype.val (Multiset.attachWith _ _ _) = _ <;>
      simp only [map_startAt, map_finishAt, Multiset.attachWith_map_val, Multiset.map_map,
        Function.comp_apply]

    · refine ⟨fᵥ.rangeSplitting, fₑ.rangeSplitting, ?_⟩
      rintro ⟨e, ⟨e, rfl⟩⟩
      rw [EVs_inc]
      have : Function.Injective (Multiset.map ⇑fᵥ) := Multiset.map_injective fᵥ.inj'
      ext1 <;> simp only [Function.Embedding.rangeSplitting_apply, map_startAt, pmap_startAt,
        map_finishAt, pmap_finishAt] <;> apply_fun (Multiset.map fᵥ) using this <;>
      simp only [← map_startAt, ← map_finishAt, ← hcomm e, Multiset.map_map, Function.comp_apply,
        Function.Embedding.rangeSplitting_eq_val] <;> clear this <;>
      change _ = Multiset.map Subtype.val (Multiset.attachWith _ _ _) <;>
      rw [Multiset.attachWith_map_val ]

  · rintro ⟨Sv, hSv, Se, hSe, hSve, ⟨⟨hGH, _hHG⟩⟩⟩
    refine ⟨⟨hGH.fᵥ.trans (Function.Embedding.subtype _), hGH.fₑ.trans (Function.Embedding.subtype _), ?_⟩⟩
    intro e
    have := hGH.comm e
    rw [EVs_inc] at this
    simp only [Function.Embedding.trans_apply, Function.Embedding.coe_subtype,
      Function.Embedding.coe_trans, map_comp]
    rw [← this, pmap_subtype_map_val]

@[simp]
lemma Qs_inc (G : Graph V E) (S : Set V) [DecidablePred (· ∈ S)] (v : V) (hv : v ∉ S) (e : E) :
    ((G.Qs S v hv).inc e).map Subtype.val = (G.inc e).map (fun u => if u ∈ S then v else u) := by
  simp only [Qs, pmap_subtype_map_val]


end Graph
