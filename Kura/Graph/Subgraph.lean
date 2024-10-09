import Kura.Conn.Walk


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W]


structure InducedSubgraph (G : Graph V E) where
  rmv : V → Bool

structure Subgraph (G : Graph V E) extends InducedSubgraph G where
  rme : E → Bool
  hrme : ∀ e v, rmv v → v ∈ G.inc e → rme e

structure QuotientGraph (G : Graph V E) where
  vmap : V → V
  vmap_idem : ∀ v, vmap (vmap v) = vmap v

structure QuotientInducedSubgraph (G : Graph V E) extends InducedSubgraph G where
  vmap : V → WithBot V
  vmap_dom : ∀ v, ¬rmv v ↔ (vmap v).isSome
  vmap_ran : ∀ v, (hdom : ¬rmv v) → ¬ rmv ((vmap v).get ((vmap_dom v).mp hdom))
  vmap_idem : ∀ v, (hdom : ¬rmv v) → vmap ((vmap v).get ((vmap_dom v).mp hdom)) = vmap v

structure QuotientSubgraph (G : Graph V E) extends Subgraph G, QuotientInducedSubgraph G where


lemma Subgraph.hrme' {G : Graph V E} (S : Subgraph G) (e : E) (he : ¬S.rme e) :
    ∀ v ∈ G.inc e, ¬S.rmv v := fun _ hv hvrm => he (S.hrme _ _ hvrm hv)

@[simp]
def QuotientGraph.vmap_idem_for_simp {G : Graph V E} (S : QuotientGraph G) (v : V) :
    S.vmap (S.vmap v) = S.vmap v := S.vmap_idem v

def QuotientGraph.ran {G : Graph V E} (S : QuotientGraph G) : Set V :=
  {v | ∃ u, S.vmap u = v}

lemma QuotientGraph.mem_ran_iff {G : Graph V E} (S : QuotientGraph G) (v : V) :
    v ∈ S.ran ↔ ∃ u, S.vmap u = v := Iff.rfl

@[simp]
lemma QuotientGraph.mem_ran_iff_vmap_self {G : Graph V E} (S : QuotientGraph G) (v : V) :
    v ∈ S.ran ↔ S.vmap v = v := by
  rw [QuotientGraph.mem_ran_iff]
  constructor
  · rintro ⟨ u, hu ⟩
    rw [← hu]
    exact S.vmap_idem u
  · rintro h
    exact ⟨ v, h ⟩

def QuotientGraph.vmap' {G : Graph V E} (S : QuotientGraph G) (v : V) : S.ran :=
  ⟨ S.vmap v, by rw [mem_ran_iff_vmap_self, vmap_idem_for_simp]⟩

def QuotientInducedSubgraph.ran {G : Graph V E} (S : QuotientInducedSubgraph G) : Set V :=
  {v | ∃ u, S.rmv u ∧ S.vmap u = some v}


def InducedSubgraph.eval {G : Graph V E} (S : InducedSubgraph G) :
  Graph {v : V // ¬S.rmv v} {e // (G.inc e).all (¬S.rmv ·) } where
  inc e := edge.pmap Subtype.mk (G.inc e.1) (by
    simpa only [Bool.not_eq_true, Bool.decide_eq_false, all_iff, Bool.not_eq_true'] using e.prop)

def Subgraph.eval {G : Graph V E} (S : Subgraph G) :
  Graph {v : V // ¬S.rmv v} {e // ¬S.rme e ∧ (G.inc e).all (¬S.rmv ·)} where
  inc e := edge.pmap Subtype.mk (G.inc e.1) (by
    simpa only [Bool.not_eq_true, Bool.decide_eq_false, all_iff, Bool.not_eq_true'] using e.2.2)

def QuotientGraph.eval {G : Graph V E} (S : QuotientGraph G) : Graph (S.ran) E where
  inc e := (G.inc e).map S.vmap'

instance InducedSubgraphFullgraph [fullGraph G] (S : InducedSubgraph G) :
  fullGraph (V := {v : V // ¬S.rmv v}) S.eval where
  all_full := sorry

instance SubgraphFullgraph [fullGraph G] (S : Subgraph G) :
  fullGraph (V := {v : V // ¬S.rmv v}) S.eval where
  all_full := sorry

instance InducedSubgraphUndirected [Undirected G] (S : InducedSubgraph G) :
  Undirected (V := {v : V // ¬S.rmv v}) S.eval where
  edge_symm := sorry

instance SubgraphUndirected [Undirected G] (S : Subgraph G) :
  Undirected (V := {v : V // ¬S.rmv v}) S.eval where
  edge_symm := sorry


variable (G : Graph V E)

def InducedSubgraph.init : InducedSubgraph G := { rmv := fun _ => false }

def Subgraph.init : Subgraph G where
  rmv := fun _ => false
  rme := fun _ => false
  hrme := by
    simp only [Bool.false_eq_true, imp_false, false_implies, implies_true]

def QuotientGraph.init : QuotientGraph G where
  vmap := id
  vmap_idem := fun _ => rfl

def QuotientInducedSubgraph.init : QuotientInducedSubgraph G where
  rmv := fun _ => false
  vmap := some
  vmap_dom := by
    simp only [Bool.false_eq_true, not_false_eq_true, Option.isSome_some, implies_true]
  vmap_ran := fun u => id
  vmap_idem := by
    simp only [Option.get_some, implies_true]

def QuotientSubgraph.init : QuotientSubgraph G where
  toSubgraph := Subgraph.init G
  vmap := some
  vmap_dom := by simp only [Subgraph.init, Bool.false_eq_true, not_false_eq_true,
    Option.isSome_some, implies_true]
  vmap_ran := fun u => id
  vmap_idem := by simp only [Option.get_some, implies_true]


variable {G : Graph V E}

def InducedSubgraph.vrm (G' : InducedSubgraph G) (v : V) : InducedSubgraph G where
  rmv u := u = v || G'.rmv u

def InducedSubgraph.vrmFinset (G' : InducedSubgraph G) (S : Finset V) : InducedSubgraph G where
  rmv u := u ∈ S || G'.rmv u

def InducedSubgraph.OnFinset (G' : InducedSubgraph G) (S : Finset V) : InducedSubgraph G where
  rmv u := u ∉ S || G'.rmv u

macro G:term "[" S:term "]" : term => `(InducedSubgraph.eval (InducedSubgraph.OnFinset (InducedSubgraph.init $G) $S))

def Subgraph.vrm (G' : Subgraph G) (v : V) : Subgraph G where
  rmv u := u = v || G'.rmv u
  rme e := v ∈ G.inc e || G'.rme e
  hrme := by
    intro e v' hv' hv'e
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hv' ⊢
    rcases hv' with rfl | h
    · exact Or.inl hv'e
    · exact Or.inr (G'.hrme _ _ h hv'e)

def Subgraph.erm [DecidableEq E] (G' : Subgraph G) (e : E) : Subgraph G where
  rmv := G'.rmv
  rme e' := e = e' || G'.rme e'
  hrme := fun v e hv hv'e => by
    rw [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr (G'.hrme v e hv hv'e)

lemma Subgraph.not_mem_erm [DecidableEq E] [fullGraph G]
  (G' : Subgraph G) (e : E) (he : ¬G'.rme e) :
    let G'' := G'.erm e
    ¬ (¬G''.rme e ∧ (G.inc e).all (¬G''.rmv ·)) := by
  sorry

/-- The second vertex is being merged into the first vertex-/
def QuotientGraph.merge (G' : QuotientGraph G) (v w : V) :
    QuotientGraph G where
  vmap u := if G'.vmap u = w then G'.vmap v else G'.vmap u
  vmap_idem u := by
    simp only
    by_cases hu : G'.vmap u = w
    · subst hu
      simp only [↓reduceIte, vmap_idem_for_simp, ite_self]
    · simp only [hu, ↓reduceIte, vmap_idem_for_simp]

def QuotientGraph.mergeSetOn (G' : QuotientGraph G) (P : V → Prop) [DecidablePred P] (x : V) :
    QuotientGraph G where
  vmap u := if P (G'.vmap u) then G'.vmap x else G'.vmap u
  vmap_idem u := by
    simp only
    by_cases hu : P (G'.vmap u)
    · simp only [hu, ↓reduceIte, vmap_idem_for_simp, ite_self]
    · simp only [hu, ↓reduceIte, vmap_idem_for_simp]

def QuotientInducedSubgraph.merge (G' : QuotientInducedSubgraph G) (v w : V) (hv : ¬G'.rmv v)
  (hw : ∃ w', ∃ (h : (G'.vmap w').isSome = true), (G'.vmap w').get h = w) :
    QuotientInducedSubgraph G where
  rmv := G'.rmv
  vmap u := if G'.vmap u = some v then some w else G'.vmap u
  vmap_dom u := by
    beta_reduce
    split_ifs with h <;>
    simp only [WithBot, vmap_dom, h, Option.isSome_some]
  vmap_ran u hu := by
    simp only at hu ⊢
    split_ifs with h
    · rcases hw with ⟨w', h', rfl⟩
      rw [Option.get_some]
      exact G'.vmap_ran w' ((G'.vmap_dom _).mpr h')
    · exact G'.vmap_ran u hu
  vmap_idem := fun u hu => by
    simp only at hu ⊢
    split_ifs with h
    · simp only [Option.get_some, ite_eq_then]
      intro hwv
      rcases hw with ⟨w', hw', rfl⟩
      rw [Option.some_get]
      exact G'.vmap_idem w' ((G'.vmap_dom _).mpr hw')
    · rw [G'.vmap_idem u hu]
      simp only [h, ↓reduceIte]

end Graph
