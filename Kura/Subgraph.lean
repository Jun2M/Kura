import Kura.Walk


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] [LinearOrder E]


structure InducedSubgraph (G : Graph V E) where
  rmv : V → Bool

structure Subgraph (G : Graph V E) extends InducedSubgraph G where
  rme : E → Bool
  hrme : ∀ e v, rmv v → v ∈ G.inc e → rme e

structure QuotientGraph (G : Graph V E) extends InducedSubgraph G where
  vmap : V → WithBot V
  vmap_dom : ∀ v, ¬rmv v ↔ (vmap v).isSome
  vmap_ran : ∀ v, (hdom : ¬rmv v) → ¬ rmv ((vmap v).get ((vmap_dom v).mp hdom))
  vmap_idem : ∀ v, (hdom : ¬rmv v) → vmap ((vmap v).get ((vmap_dom v).mp hdom)) = vmap v

structure QuotientSubgraph (G : Graph V E) extends Subgraph G, QuotientGraph G where

structure Minor (G : Graph V E) [fullGraph G] extends QuotientSubgraph G where
  ctt_path (v) (hdom : ¬rmv v) : G.Path
  path_rme (v : V) (hdom : ¬rmv v) : ∀ e ∈ (ctt_path v hdom).edges, rme e
  path_ctv (v : V) (hdom : ¬rmv v) : ∀ u ∈ (ctt_path v hdom).vertices, vmap u = vmap v
  path_start (v : V) (hdom : ¬rmv v) : (ctt_path v hdom).start = v
  path_finish (v : V) (hdom : ¬rmv v) :
    (ctt_path v hdom).finish = (vmap v).get ((vmap_dom v).mp hdom)


lemma Subgraph.hrme' {G : Graph V E} (S : Subgraph G) (e : E) (he : ¬S.rme e) :
    ∀ v ∈ G.inc e, ¬S.rmv v := fun _ hv hvrm => he (S.hrme _ _ hvrm hv)

def QuotientGraph.ran {G : Graph V E} (S : QuotientGraph G) : Set V :=
  {v | ∃ u, S.rmv u ∧ S.vmap u = some v}


def InducedSubgraph.eval {G : Graph V E} (S : InducedSubgraph G) :
  Graph {v : V // ¬S.rmv v} {e // (G.inc e).all (¬S.rmv ·) } where
  inc e := edge.pmap Subtype.mk (G.inc e.1) (by
    simpa only [Bool.not_eq_true, Bool.decide_eq_false, all_iff, Bool.not_eq_true'] using e.prop)

def Subgraph.eval {G : Graph V E} (S : Subgraph G) :
  Graph {v : V // ¬S.rmv v} {e // ¬S.rme e ∧ (G.inc e).all (¬S.rmv ·)} where
  inc e := edge.pmap Subtype.mk (G.inc e.1) (by
    simpa only [Bool.not_eq_true, Bool.decide_eq_false, all_iff, Bool.not_eq_true'] using e.2.2)

def Minor.eval [Fintype V] {G : Graph V E} [fullGraph G] (S : Minor G) :
  Graph {v : V // ∃ u, S.vmap u = some v}
    {e // ¬S.rme e ∧ (G.inc e).all (fun v => ∃ u, S.vmap u = some v)} where
  inc e :=
    let ⟨e, _hrme, hran⟩ := e
    edge.pmap Subtype.mk (G.inc e) (by simpa only [all_iff, decide_eq_true_eq] using hran)

instance InducedSubgraphFullgraph [fullGraph G] (S : InducedSubgraph G) :
  fullGraph (V := {v : V // ¬S.rmv v}) S.eval where
  all_full := sorry

instance SubgraphFullgraph [fullGraph G] (S : Subgraph G) :
  fullGraph (V := {v : V // ¬S.rmv v}) S.eval where
  all_full := sorry

instance MinorFullgraph [Fintype V] [fullGraph G] (S : Minor G) :
  fullGraph (V := {v : V // ∃ u, S.vmap u = some v}) S.eval where
  all_full := sorry

instance InducedSubgraphUndirected [Undirected G] (S : InducedSubgraph G) :
  Undirected (V := {v : V // ¬S.rmv v}) S.eval where
  edge_symm := sorry

instance SubgraphUndirected [Undirected G] (S : Subgraph G) :
  Undirected (V := {v : V // ¬S.rmv v}) S.eval where
  edge_symm := sorry

instance MinorUndirected [Fintype V] [Undirected G] [fullGraph G] (S : Minor G) :
  Undirected (V := {v : V // ∃ u, S.vmap u = some v}) S.eval where
  edge_symm := sorry

variable (G : Graph V E)

def InducedSubgraph.init : InducedSubgraph G := { rmv := fun _ => false }

def Subgraph.init : Subgraph G where
  rmv := fun _ => false
  rme := fun _ => false
  hrme := by
    simp only [Bool.false_eq_true, imp_false, false_implies, implies_true]

def QuotientGraph.init : QuotientGraph G where
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

def Minor.init [fullGraph G] : Minor G where
  toQuotientSubgraph := QuotientSubgraph.init G
  ctt_path v _hdom := Graph.Path.nil v
  path_rme v hdom e he := (List.not_mem_nil e he).elim
  path_ctv v hdom u hu := ((Path.mem_nil_vertices v u).mp hu) ▸ rfl
  path_start v hdom := rfl
  path_finish v _hdom := by simp only [Walk.finish, QuotientSubgraph.init, Path.nil, Walk.nil,
    Option.get_some]

variable {G : Graph V E}

def InducedSubgraph.vrm (G' : InducedSubgraph G) (v : V) : InducedSubgraph G where
  rmv u := u = v || G'.rmv u

def InducedSubgraph.vrmFinset (G' : InducedSubgraph G) (S : Finset V) : InducedSubgraph G where
  rmv u := u ∈ S || G'.rmv u

def InducedSubgraph.OnFinset (G' : InducedSubgraph G) (S : Finset V) : InducedSubgraph G where
  rmv u := u ∉ S || G'.rmv u

local macro G:term "[" S:term "]" : term => `(InducedSubgraph.eval (InducedSubgraph.OnFinset (InducedSubgraph.init $G) $S))

#eval! (CompleteGraph 4)[({0, 1, 2} : Finset (Fin 4))]

def Subgraph.vrm (G' : Subgraph G) (v : V) : Subgraph G where
  rmv u := u = v || G'.rmv u
  rme e := v ∈ G.inc e || G'.rme e
  hrme := by
    intro e v' hv' hv'e
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hv' ⊢
    rcases hv' with rfl | h
    · exact Or.inl hv'e
    · exact Or.inr (G'.hrme _ _ h hv'e)

def Subgraph.erm (G' : Subgraph G) (e : E) : Subgraph G where
  rmv := G'.rmv
  rme e' := e = e' || G'.rme e'
  hrme := fun v e hv hv'e => by
    rw [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr (G'.hrme v e hv hv'e)

lemma Subgraph.not_mem_erm [fullGraph G] (G' : Subgraph G) (e : E) (he : ¬G'.rme e) :
    let G'' := G'.erm e
    ¬ (¬G''.rme e ∧ (G.inc e).all (¬G''.rmv ·)) := by
  sorry

def QuotientGraph.merge (G' : QuotientGraph G) (v w : V) (hv : ¬G'.rmv v)
  (hw : ∃ w', ∃ (h : (G'.vmap w').isSome = true), (G'.vmap w').get h = w) : QuotientGraph G where
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

def Minor.vrm [fullGraph G] (G' : Minor G) (v : V) : Minor G where
  rmv u := G'.vmap u = G'.vmap v || G'.rmv u
  rme e := G'.vmap v ∈ (G.inc e).map G'.vmap || G'.rme e
  hrme e v' hv' hv'e := by
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hv' ⊢
    rcases hv' with h | h
    · left
      exact h ▸ edge.mem_map_of_mem G'.vmap v' (G.inc e) hv'e
    · right
      exact (G'.hrme e v' h hv'e)
  vmap u := if G'.vmap u = G'.vmap v then none else G'.vmap u
  vmap_dom u := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
    split_ifs with h
    · simp only [h, not_true_eq_false, false_and, Option.isSome_none, Bool.false_eq_true]
    · simp only [h, not_false_eq_true, G'.vmap_dom u, true_and]
  vmap_ran u hu := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hu ⊢
    obtain ⟨hmap, hdom⟩ := hu
    split_ifs
    rw [G'.vmap_idem u hdom]
    exact ⟨hmap, G'.vmap_ran u hdom⟩
  vmap_idem u hu := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hu ⊢
    obtain ⟨hmap, hdom⟩ := hu
    split_ifs
    simp only [G'.vmap_idem u hdom, hmap, ↓reduceIte]
  ctt_path u hdom := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hdom
    exact if G'.vmap u = G'.vmap v then Graph.Path.nil u else G'.ctt_path u hdom.2
  path_ctv u hdom v' hv' := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hdom
    simp [hdom.1] at hv'
    simp only [hdom.1, ↓reduceIte, G'.path_ctv u hdom.2 v' hv']
  path_rme u hdom e he := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hdom
    obtain ⟨hmap, hdom⟩ := hdom
    simp only [hmap, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at he ⊢
    right
    exact G'.path_rme u hdom e he
  path_start u hdom := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hdom
    simp only [hdom, ↓reduceIte]
    exact G'.path_start u hdom.2
  path_finish := fun u hdom => by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hdom
    simp only [hdom, ↓reduceIte]
    exact G'.path_finish u hdom.2

def Minor.erm [fullGraph G] (G' : Minor G) (e : E) : Minor G where
  rmv := G'.rmv
  rme e' := e = e' || G'.rme e'
  hrme e' u hu he' := by
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hu ⊢
    right
    exact G'.hrme e' u hu he'
  vmap := G'.vmap
  vmap_dom := G'.vmap_dom
  vmap_ran := G'.vmap_ran
  vmap_idem := G'.vmap_idem
  ctt_path := G'.ctt_path
  path_ctv := G'.path_ctv
  path_rme u hu e' he' := by
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hu ⊢
    right
    exact G'.path_rme u hu e' he'
  path_start := G'.path_start
  path_finish := G'.path_finish

def Minor.ctt [Undirected G] (G' : Minor G) (e : E) (he : ¬G'.rme e) : Minor G where
  rmv := G'.rmv
  rme e' := e = e' || G'.rme e'
  hrme e' u hu he' := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    right
    exact G'.hrme e' u hu he'
  vmap u :=
    let (v, w) := (Sym2.sortEquiv (G.get e)).val
    if G'.vmap u = G'.vmap v then G'.vmap w else G'.vmap u
  vmap_dom u := by
    simp only [Sym2.sortEquiv_apply_coe]
    split_ifs with h
    · rw [G'.vmap_dom u, h, ← G'.vmap_dom, ← G'.vmap_dom]
      simp only [G'.hrme' e he (G.get e).inf (G.get_inf_mem_inc e), Bool.false_eq_true,
        not_false_eq_true, G'.hrme' e he (G.get e).sup (G.get_sup_mem_inc e)]
    · exact G'.vmap_dom u
  vmap_ran u hu hrmv := by
    simp only [Sym2.sortEquiv_apply_coe] at hu hrmv
    split_ifs at hrmv with h
    · refine G'.vmap_ran (v := (G.get e).sup) ?_ hrmv
      exact G'.hrme' e he (G.get e).sup (G.get_sup_mem_inc e)
    · exact G'.vmap_ran u hu hrmv
  vmap_idem u hu := by
    simp only [Sym2.sortEquiv_apply_coe] at hu ⊢
    split_ifs with h
    · simp only [Option.get_some, ite_eq_then]
      exact fun _ => G'.vmap_idem _ (G'.hrme' e he (G.get e).sup (G.get_sup_mem_inc e))
    · simp only [G'.vmap_idem u hu, h, ↓reduceIte]
  ctt_path u hdom := by
    if h : G'.vmap u = G'.vmap (G.get e).inf then
      let A := G'.ctt_path u hdom
      let B := G'.ctt_path (G.get e).inf (G'.hrme' e he (G.get e).inf (G.get_inf_mem_inc e))
      let AB := A.append B.reverse (by
        rw [Path.reverse_start, G'.path_finish u hdom,
          G'.path_finish (G.get e).inf (G'.hrme' e he (G.get e).inf (G.get_inf_mem_inc e))]
        apply_fun some using Option.some_injective _
        rwa [Option.some_get, Option.some_get])
      if hloop : (G.get e).inf = (G.get e).sup then
        exact A
      else
        let C := Path.some (G := G) (G.get e).inf e (G.get e).sup sorry sorry
        let ABC := AB.append C (by
        rw [Path.append_finish, Path.reverse_finish, G'.path_start]
        rfl)
        exact ABC.append (G'.ctt_path (G.get e).sup (G'.hrme' e he (G.get e).sup (G.get_sup_mem_inc e))) (by
          rw [Path.append_finish, G'.path_start (G.get e).sup (G'.hrme' e he (G.get e).sup (G.get_sup_mem_inc e)), Path.some_finish])
    else
      exact G'.ctt_path u hdom
  path_ctv u hdom v' hv' := by
    simp only at hdom
    simp only [Sym2.sortEquiv_apply_coe]
    split_ifs with hv'inf huinf huinf
    · rfl
    · simp [hv'inf, huinf] at hv'
      have := G'.path_ctv u hdom v' hv'
      exfalso
      exact (this ▸ huinf) hv'inf
    · simp [hv'inf, huinf] at hv'
      split_ifs at hv' with h1
      · rw [← h1]
        rw [← huinf]
        exact G'.path_ctv u hdom v' hv'
      · simp only [Path.mem_append_vertices, Path.mem_reverse_vertices, Path.mem_some_vertices] at hv'
        rcases hv' with ((hv'u | hv'inf') | (hv'eqinf | hv'eqsup)) | hv'sup
        · exfalso
          have := G'.path_ctv u hdom v' hv'u
          exact hv'inf (this ▸ huinf)
        · exfalso
          exact hv'inf (G'.path_ctv (G.get e).inf (G'.hrme' e he (G.get e).inf (G.get_inf_mem_inc e)) v' hv'inf')
        · rw [hv'eqinf] at hv'inf
          exact (hv'inf rfl).elim
        · subst v'
          rfl
        · exact G'.path_ctv (G.get e).sup (G'.hrme' e he (G.get e).sup (G.get_sup_mem_inc e)) v' hv'sup
    · simp [hv'inf, huinf] at hv'
      exact G'.path_ctv u hdom v' hv'
  path_rme := fun u hdom e' he' => by
    simp at he' ⊢
    split_ifs at he' with h1 h2
    · right
      exact G'.path_rme u hdom e' he'
    · simp only [Path.mem_append_edges, Path.mem_reverse_edges] at he'
      rcases he' with ((he' | he') | he') | he'
      · right
        exact G'.path_rme u hdom e' he'
      · right
        exact G'.path_rme (G.get e).inf (G'.hrme' e he (G.get e).inf (G.get_inf_mem_inc e)) e' he'
      · left
        rwa [Path.mem_some_edges, Eq.comm] at he'
      · right
        exact G'.path_rme (G.get e).sup (G'.hrme' e he (G.get e).sup (G.get_sup_mem_inc e)) e' he'
    · right
      exact G'.path_rme u hdom e' he'
  path_start u hdom := by
    simp only [dite_eq_ite]
    split_ifs with h1 h2 <;>
    try {simp only [Path.append_start]} <;>
    exact G'.path_start u hdom
  path_finish u hdom := by
    simp only [Bool.not_eq_true, dite_eq_ite, Sym2.sortEquiv_apply_coe]
    split_ifs with h1 h2
    · rw [G'.path_finish u hdom]
      congr 1
      rw [h1]
      congr 1
    · simp only [Path.append_finish]
      exact G'.path_finish (G.get e).sup (G'.hrme' e he (G.get e).sup (G.get_sup_mem_inc e))
    · exact G'.path_finish u hdom

local macro G:term "/ᵍ" e:term : term => `(Minor.eval (Minor.ctt (Minor.init $G) $e sorry))

#eval! (CompleteGraph 4) /ᵍ ⟨0, Nat.choose_pos (by norm_num)⟩

lemma Minor.inf_not_mem_ctt [Undirected G] [fullGraph G] (G' : Minor G) (e : E)
  (he : ¬G'.rme e) : ¬ ∃ u, (G'.ctt e he).vmap u = some ((G.get e).inf) := by
  sorry


def hasMinor [Fintype V] (G : Graph V E) [fullGraph G] (H : Graph W F) : Prop := ∃ (S : Minor G), Nonempty (Isom S.eval H)

class NConnected (G : Graph V E) [Fintype V] [fullGraph G] (n : ℕ) : Prop where
  h : ∀ S : Finset V, S.card ≤ n → G[Sᶜ].connected

end Graph
