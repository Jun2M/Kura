import Kura.Conn.Walk


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

def Es (G : Graph V E) (S : Set E) [DecidablePred (· ∈ S)] : Graph V S where
  inc := (G.inc ·.val)

macro G:term "{" S:term "}ᴳ" : term => `(Graph.Es $G $S)

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

-- Merges to the start of the path
def Ms (G : Graph V E) [DecidableEq E] (P : G.Path) :
    Graph {v : V // v ∉ P.vertices.tail} {e : E // e ∉ P.edges} where
  inc e := G
    |>.Qs {v : V | v ∈ P.vertices.tail} P.start P.start_not_mem_vertices_tail
    |>.Es {e : E | e ∉ P.edges}
    |>.inc e

-- contraction by a rooted tree?

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
    simp only [all, Function.Embedding.coeFn_mk, map, Vs_inc]

@[simp]
lemma Es_inc (G : Graph V E) (S : Set E) [DecidablePred (· ∈ S)] (e : S) :
    (G{S}ᴳ).inc e = G.inc e := by rfl

def Es_subgraph (G : Graph V E) (S : Set E) [DecidablePred (· ∈ S)] : G{S}ᴳ ⊆ᴳ G where
  fᵥ := { toFun := id, inj' := fun e₁ e₂ h => h }
  fₑ := { toFun := Subtype.val, inj' := fun e₁ e₂ h => SetCoe.ext h }
  comm := by
    rintro ⟨e, _he⟩
    simp only [Function.Embedding.coeFn_mk, map, Es_inc, map_id]

@[simp]
lemma EVs_inc (G : Graph V E) (Sv : Set V) [DecidablePred (· ∈ Sv)] (Se : Set E)
  [DecidablePred (· ∈ Se)] (he : ∀ e ∈ Se, G.all e (· ∈ Sv)) (e : Se) :
    (G.EVs Sv Se he).inc e = G.pmap Subtype.mk e (by
      specialize he e.val e.prop; simpa only [all, all_iff, decide_eq_true_eq] using he) := by rfl

lemma aux (G : Graph V E) (H : Graph W F) (S : G ⊆ᴳ H) (e : E)
  (hcomm : H.inc (S.fₑ e) = G.map e S.fᵥ) :
    H.pmap Subtype.mk ↑(S.fₑ.rangeFactorization e) sorry = G.map e S.fᵥ.rangeFactorization := by
  by_cases h : (G.map e S.fᵥ).isDir
  · obtain ⟨a, b, hab⟩ := exist_of_isDir _ h
    rw [eq_comm] at hcomm
    change G.map e S.fᵥ = dir (a, b) at hab
    simp only [map, map_eq_dir] at hab
    obtain ⟨a', b', hab', rfl, rfl⟩ := hab
    simp only [pmap, Function.Embedding.rangeFactorization_apply, map, hab', map_dir, pmap_eq_dir]
    use a'.map S.fᵥ, b'.map S.fᵥ, by rw [← hcomm]; simp only [map, hab', map_dir]
    constructor
    · exact (Option.map_rangeFactorization S.fᵥ a').symm
    · exact (Option.map_rangeFactorization S.fᵥ b').symm
  · rw [not_isDir_iff_isUndir] at h
    obtain ⟨s, hs⟩ := exist_of_isUndir _ h
    clear h
    simp at hs
    obtain ⟨s', hs', rfl⟩ := hs
    simp only [map, hs', map_undir, pmap, pmap_eq_undir_iff] at hcomm ⊢
    use s'.map (S.fᵥ), (by rwa [Function.Embedding.rangeFactorization_coe])
    exact (Sym2.map_rangeFactorization S.fᵥ s').symm

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
      obtain ⟨v, hv, rfl⟩ := hw
      use v
    · refine ⟨fᵥ.rangeFactorization, fₑ.rangeFactorization, ?_⟩
      intro e
      rw [EVs_inc]
      apply aux G H ⟨fᵥ, fₑ, hcomm⟩ e (hcomm e)

    · refine ⟨(fᵥ.rangeFactorization.equivOfSurjective fᵥ.rangeFactorization_surj).symm.toEmbedding,
        (fₑ.rangeFactorization.equivOfSurjective fₑ.rangeFactorization_surj).symm.toEmbedding, ?_⟩
      rintro ⟨e, ⟨e, rfl⟩⟩
      simp only [Equiv.coe_toEmbedding, map, EVs_inc, pmap]
      sorry
  ·
    sorry

end Graph
