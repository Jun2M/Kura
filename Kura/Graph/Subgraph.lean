import Kura.Conn.Walk


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W]


/--
If removeV v = true, v is removed when InducedSubgraph is evaluated-/
structure InducedSubgraph (G : Graph V E) where
  Vset : Set V
  DecVMem : DecidablePred (· ∈ Vset)

structure Subgraph (G : Graph V E) extends InducedSubgraph G where
  Eset : Set E
  DecEMem : DecidablePred (· ∈ Eset)
  Eset_spec : ∀ e ∈ Eset, ∀ v ∈ G.inc e, v ∈ Vset

structure QuotientGraph (G : Graph V E) where
  vmap : V → V
  vmap_idem : ∀ v, vmap (vmap v) = vmap v

/-- If v is mapped to ⊥ = none, remove it -/
structure QuotientSubgraph (G : Graph V E) where
  vmap' : V → WithBot V
  vmap'_idem : ∀ v, Option.bind (vmap' v) vmap' = vmap' v
  Eset : Set E
  DecEMem : DecidablePred (· ∈ Eset)
  Eset_spec : ∀ e ∈ Eset, ∀ v ∈ G.inc e, (vmap' v).isSome

----------------------------------------------------------------------
-- useful lemma

variable {G : Graph V E}

lemma Subgraph.not_mem_Eset  (S : Subgraph G) (he : ∃ v ∈ G.inc e, v ∉ S.Vset) :
    e ∉ S.Eset := by
  intro h
  absurd S.Eset_spec e h
  push_neg
  exact he

lemma QuotientSubgraph.not_mem_Eset (S : QuotientSubgraph G) (he : ∃ v ∈ G.inc e, (S.vmap' v).isNone) :
    e ∉ S.Eset := by
  intro h
  absurd S.Eset_spec e h
  push_neg
  simpa only [ne_eq, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none] using he

/-- Expose the decidability of (· ∈ Vset) -/
instance InducedSubgraphDecVMem {G : Graph V E} (S : InducedSubgraph G) :
    DecidablePred (· ∈ S.Vset) := S.DecVMem

/-- Expose the decidability of (· ∈ Eset)-/
instance SubgraphDecEMem (S : Subgraph G) : DecidablePred (· ∈ S.Eset) := S.DecEMem

/-- Make vmap_idem simp-avaliable-/
@[simp]
lemma QuotientGraph.vmap_idem_for_simp  (S : QuotientGraph G) (v : V) :
    S.vmap (S.vmap v) = S.vmap v := S.vmap_idem v

/-- Expose the decidability of (· ∈ Eset)-/
instance QuotientSubgraphDecEMem (S : QuotientSubgraph G) : DecidablePred (· ∈ S.Eset) := S.DecEMem

-------------------------------------------------
-- Evaluations

def InducedSubgraph.eval (S : InducedSubgraph G) :
  Graph S.Vset {e // (G.inc e).all (· ∈ S.Vset) } where
  inc e := edge.pmap Subtype.mk (G.inc e.1) (by
    simpa only [all_iff, decide_eq_true_eq] using e.prop)

def Subgraph.eval (S : Subgraph G) :
  Graph S.Vset S.Eset where
  inc e := edge.pmap Subtype.mk (G.inc e.1) (S.Eset_spec e.val e.prop)

-- some setup is needed to make this work for QuotientGraph
def QuotientGraph.ran (S : QuotientGraph G) : Set V :=
  {v | ∃ u, S.vmap u = v}

lemma QuotientGraph.mem_ran_iff (S : QuotientGraph G) (v : V) :
    v ∈ S.ran ↔ ∃ u, S.vmap u = v := Iff.rfl

@[simp]
lemma QuotientGraph.mem_ran_iff_vmap_self (S : QuotientGraph G) (v : V) :
    v ∈ S.ran ↔ S.vmap v = v := by
  rw [QuotientGraph.mem_ran_iff]
  constructor
  · rintro ⟨ u, hu ⟩
    rw [← hu]
    exact S.vmap_idem u
  · rintro h
    exact ⟨ v, h ⟩

def QuotientGraph.vmapRan (S : QuotientGraph G) (v : V) : S.ran :=
  ⟨ S.vmap v, by rw [mem_ran_iff_vmap_self, vmap_idem_for_simp]⟩

def QuotientGraph.eval (S : QuotientGraph G) : Graph (S.ran) E where
  inc e := (G.inc e).map S.vmapRan

-- Even more setup is needed to make this work for QuotientSubgraph
def QuotientSubgraph.ran (S : QuotientSubgraph G) : Set V :=
  {v | ∃ u, S.vmap' u = some v}

def QuotientSubgraph.Vset (S : QuotientSubgraph G) : Set V :=
  {v | (S.vmap' v).isSome }

@[simp]
lemma QuotientSubgraph.mem_Vset_iff (S : QuotientSubgraph G) (v : V) :
    v ∈ S.Vset ↔ (S.vmap' v).isSome := Iff.rfl

/-- if e is in Eset, all vertices incident to e is not removed.
  Embed this fact to the type of each v. -/
def QuotientSubgraph.domSubtype (S : QuotientSubgraph G) (e : S.Eset) : edge S.Vset :=
  (G.inc e).pmap Subtype.mk (fun v hv => S.Eset_spec e.val e.prop v hv)

def QuotientSubgraph.vmap'Ran (S : QuotientSubgraph G) (v : S.Vset) : S.ran :=
  ⟨ (S.vmap' v.val).get v.prop, by simp only [ran, Set.mem_setOf_eq, Option.some_get,
    exists_apply_eq_apply]⟩

def QuotientSubgraph.eval (S : QuotientSubgraph G) : Graph S.ran S.Eset where
  inc e := S.domSubtype e |>.map S.vmap'Ran

------------------------------------------------------------------------
-- Carrying over the instances

instance InducedSubgraphFullgraph [fullGraph G] (S : InducedSubgraph G) :
  fullGraph (V := S.Vset) S.eval where
  all_full := sorry

instance SubgraphFullgraph [fullGraph G] (S : Subgraph G) :
  fullGraph (V := S.Vset) S.eval where
  all_full := sorry

instance QuotientGraphFullgraph [fullGraph G] (S : QuotientGraph G) :
  fullGraph (V := S.ran) S.eval where
  all_full := sorry

instance QuotientSubgraphFullgraph [fullGraph G] (S : QuotientSubgraph G) :
  fullGraph (V := S.ran) S.eval where
  all_full := sorry

instance InducedSubgraphUndirected [Undirected G] (S : InducedSubgraph G) :
  Undirected (V := S.Vset) S.eval where
  edge_symm := sorry

instance SubgraphUndirected [Undirected G] (S : Subgraph G) :
  Undirected (V := S.Vset) S.eval where
  edge_symm := sorry

instance QuotientGraphUndirected [Undirected G] (S : QuotientGraph G) :
  Undirected (V := S.ran) S.eval where
  edge_symm := sorry

instance QuotientSubgraphUndirected [Undirected G] (S : QuotientSubgraph G) :
  Undirected (V := S.ran) S.eval where
  edge_symm := sorry

-----------------------------------------------------------------------------
-- Initializations

variable (G : Graph V E)

def InducedSubgraph.init : InducedSubgraph G where
  Vset := Set.univ
  DecVMem := by infer_instance

def Subgraph.init : Subgraph G where
  Vset := Set.univ
  DecVMem := by infer_instance
  Eset := Set.univ
  DecEMem := by infer_instance
  Eset_spec := by simp only [Set.mem_univ, implies_true, imp_self]

def QuotientGraph.init : QuotientGraph G where
  vmap := id
  vmap_idem := fun _ => rfl

def QuotientSubgraph.init : QuotientSubgraph G where
  vmap' := some
  vmap'_idem := by simp only [Option.bind_some, implies_true]
  Eset := Set.univ
  DecEMem := by infer_instance
  Eset_spec := by simp only [Set.mem_univ, Option.isSome_some, implies_true, imp_self]

-----------------------------------------------------------------------------
-- Elementary operations

variable {G : Graph V E}

def InducedSubgraph.vrm (G' : InducedSubgraph G) (v : V) : InducedSubgraph G where
  Vset := G'.Vset \ {v}
  DecVMem := by infer_instance

def InducedSubgraph.OnSet (G' : InducedSubgraph G) (S : Set V) [DecidablePred (· ∈ S)] :
    InducedSubgraph G where
  Vset := G'.Vset ∩ S
  DecVMem := by infer_instance

macro G:term "[" S:term "]ᴳ" : term =>
  `(InducedSubgraph.eval (InducedSubgraph.OnSet (InducedSubgraph.init $G) $S))


def Subgraph.vrm (G' : Subgraph G) (v : V) : Subgraph G where
  Vset := G'.Vset \ {v}
  DecVMem := by infer_instance
  Eset := {e ∈ G'.Eset | G.all e (· ≠ v)}
  DecEMem := by infer_instance
  Eset_spec e he u hu := by
    simp only [all, ne_eq, decide_not, all_iff, Bool.not_eq_true', decide_eq_false_iff_not,
      Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff] at he ⊢
    constructor
    · exact G'.Eset_spec e he.1 u hu
    · exact he.2 u hu

def Subgraph.OnSetV (G' : Subgraph G) (S : Set V) [DecidablePred (· ∈ S)] : Subgraph G where
  Vset := G'.Vset ∩ S
  DecVMem := by infer_instance
  Eset := {e ∈ G'.Eset | G.all e (· ∈ S)}
  DecEMem := by infer_instance
  Eset_spec e he u hu := by
    simp only [all, all_iff, decide_eq_true_eq, Set.mem_setOf_eq, Set.mem_inter_iff] at he ⊢
    constructor
    · exact G'.Eset_spec e he.1 u hu
    · exact he.2 u hu

def Subgraph.erm [DecidableEq E] (G' : Subgraph G) (e : E) : Subgraph G where
  Vset := G'.Vset
  DecVMem := by infer_instance
  Eset := G'.Eset \ {e}
  DecEMem := by infer_instance
  Eset_spec e' he' u hu := by
    simp only [Set.mem_diff, Set.mem_singleton_iff] at he'
    exact G'.Eset_spec e' he'.1 u hu

def Subgraph.OnSetE (G' : Subgraph G) (S : Set E) [DecidablePred (· ∈ S)] : Subgraph G where
  Vset := G'.Vset
  DecVMem := by infer_instance
  Eset := G'.Eset ∩ S
  DecEMem := by infer_instance
  Eset_spec e he u hu := by
    simp only [Set.mem_inter_iff] at he
    exact G'.Eset_spec e he.1 u hu

macro G:term "{" S:term "}ᴳ" : term => `(Subgraph.eval (Subgraph.OnSetE (Subgraph.init $G) $S))

/-- The second vertex is being merged into the first vertex-/
def QuotientGraph.merge (G' : QuotientGraph G) (v w : V) :
    QuotientGraph G where
  vmap u := if G'.vmap u = w then G'.vmap v else G'.vmap u
  vmap_idem u := by
    by_cases hu : G'.vmap u = w <;> simp only [hu, ↓reduceIte, vmap_idem_for_simp, ite_self]

def QuotientGraph.mergeOnSet (G' : QuotientGraph G) (S : Set V) [DecidablePred (· ∈ S)] (x : V) :
    QuotientGraph G where
  vmap u := if G'.vmap u ∈ S then G'.vmap x else G'.vmap u
  vmap_idem u := by
    by_cases hu : G'.vmap u ∈ S <;> simp only [hu, ↓reduceIte, vmap_idem_for_simp, ite_self]


def QuotientSubgraph.vrm [DecidableEq E] (G' : QuotientSubgraph G) (v : V) :
    QuotientSubgraph G where
  vmap' u := if G'.vmap' u = v then ⊥ else G'.vmap' u
  vmap'_idem u := by
    by_cases hu : G'.vmap' u = v <;> simp [hu, ↓reduceIte]
    · rfl
    · by_cases hvu : (G'.vmap' u) = none
      · simp only [hvu, Option.none_bind]
      · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists.mp hvu
        simp only [← hw, Option.some_bind]
        sorry
  Eset := {e ∈ G'.Eset | G.all e (G'.vmap' · ≠ v)}
  DecEMem := by infer_instance
  Eset_spec e he u hu := by
    simp only [ne_eq, decide_not, all_iff, Bool.not_eq_true', decide_eq_false_iff_not,
      Set.mem_setOf_eq] at he
    simp only [he.2 u hu, ↓reduceIte]
    exact G'.Eset_spec e he.1 u hu

------------------------------------------------------------------------
-- Lemmas about the elementary operations

lemma Subgraph.not_mem_erm [DecidableEq E] [fullGraph G] (G' : Subgraph G) (e : E) :
    let G'' := G'.erm e
    ¬ (e ∈ G''.Eset ∧ (G.inc e).all (· ∈ G''.Vset)) := by
  simp only [all_iff, decide_eq_true_eq, not_and, not_forall, Classical.not_imp]
  rintro h

  sorry

-- def deleteEdges (G: Graph V E) (S : Set E) [DecidablePred (· ∈ S)] : Subgraph G :=
--   (Subgraph.init G).OnSetE Sᶜ


end Graph
