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
  Eset_spec : ∀ e v, vmap' v = ⊥ → v ∈ G.inc e → e ∉ Eset

----------------------------------------------------------------------
-- useful lemma

variable {G : Graph V E}

lemma Subgraph.not_mem_Eset  (S : Subgraph G) (he : ∃ v ∈ G.inc e, v ∉ S.Vset) :
    e ∉ S.Eset := by
  intro h
  absurd S.Eset_spec e h
  push_neg
  exact he

/-- Expose the decidability of (· ∈ Vset) -/
instance InducedSubgraphDecVMem {G : Graph V E} (S : InducedSubgraph G) :
    DecidablePred (· ∈ S.Vset) := S.DecVMem

/-- Expose the decidability of (· ∈ Eset)-/
instance SubgraphDecEMem (S : Subgraph G) : DecidablePred (· ∈ S.Eset) := S.DecEMem

/-- Make vmap_idem simp-avaliable-/
@[simp]
lemma QuotientGraph.vmap_idem_for_simp  (S : QuotientGraph G) (v : V) :
    S.vmap (S.vmap v) = S.vmap v := S.vmap_idem v

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

def QuotientGraph.vmap' (S : QuotientGraph G) (v : V) : S.ran :=
  ⟨ S.vmap v, by rw [mem_ran_iff_vmap_self, vmap_idem_for_simp]⟩

def QuotientSubgraph.ran (S : QuotientSubgraph G) : Set V :=
  {v | ∃ u, S.vmap' u = some v}


-------------------------------------------------
-- Evaluations

def InducedSubgraph.eval (S : InducedSubgraph G) :
  Graph S.Vset {e // (G.inc e).all (· ∈ S.Vset) } where
  inc e := edge.pmap Subtype.mk (G.inc e.1) (by
    simpa only [all_iff, decide_eq_true_eq] using e.prop)

def Subgraph.eval (S : Subgraph G) :
  Graph S.Vset S.Eset where
  inc e := edge.pmap Subtype.mk (G.inc e.1) (S.Eset_spec e.val e.prop)

def QuotientGraph.eval (S : QuotientGraph G) : Graph (S.ran) E where
  inc e := (G.inc e).map S.vmap'

instance InducedSubgraphFullgraph [fullGraph G] (S : InducedSubgraph G) :
  fullGraph (V := S.Vset) S.eval where
  all_full := sorry

instance SubgraphFullgraph [fullGraph G] (S : Subgraph G) :
  fullGraph (V := S.Vset) S.eval where
  all_full := sorry

instance InducedSubgraphUndirected [Undirected G] (S : InducedSubgraph G) :
  Undirected (V := S.Vset) S.eval where
  edge_symm := sorry

instance SubgraphUndirected [Undirected G] (S : Subgraph G) :
  Undirected (V := S.Vset) S.eval where
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
  Eset_spec := by simp only [reduceCtorEq, Set.mem_univ, not_true_eq_false, imp_false,
    false_implies, implies_true]

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

macro G:term "[" S:term "]" : term =>
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

macro G:term "{" S:term "}" : term => `(Subgraph.eval (Subgraph.OnSetE (Subgraph.init $G) $S))

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
