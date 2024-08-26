import Mathlib
import Wagner.MulDigraph


@[ext]
structure MultiGraph (V : Type*) (E : Type*) where
  inc : E → Sym2 V

namespace MultiGraph

variable {V : Type*} {E : Type*}

noncomputable def assignDi (G : MultiGraph V E) : MulDigraph V E :=
  { inc := λ e => (G.inc e).out }

noncomputable def toMulDigraph (G : MultiGraph V E) : MulDigraph V (E × Bool) :=
  { inc := λ e => if e.2 then (G.inc e.1).out.swap else (G.inc e.1).out }

def adj (G : MultiGraph V E) (v w : V) : Prop :=
  ∃ (e : E), G.inc e = s(v, w)

lemma adj_comm (G : MultiGraph V E) (v w : V) :
  G.adj v w ↔ G.adj w v := by
  unfold adj
  rw [Sym2.eq_swap]
  done

lemma flip_adj (G : MultiGraph V E) :
  flip G.adj = G.adj := by
  funext v w
  unfold flip
  rw [adj_comm]
  done

lemma adj_iff_assignDi_adj_or_adj_comm (G : MultiGraph V E) (v w : V) :
  G.adj v w ↔ (G.assignDi.adj v w ∨ G.assignDi.adj w v) := by
  unfold assignDi adj MulDigraph.adj
  simp only
  rw [← exists_or]
  exact exists_congr (λ e => Sym2.eq_iff_out_eq_or_out_swap _ _ _)
  done

lemma adj_iff_toMulDigraph_adj (G : MultiGraph V E) (v w : V) :
  G.adj v w ↔ G.toMulDigraph.adj v w := by
  unfold adj toMulDigraph MulDigraph.adj
  simp only [Prod.exists, Bool.exists_bool, ↓reduceIte]
  apply exists_congr
  intro e
  rw [eq_comm, Iff.comm, eq_comm, @eq_comm _ (G.inc e).out.swap, ← Sym2.mk_eq_mk_iff]
  simp only [Quot.out_eq]
  done


def isLoop (G : MultiGraph V E) (e : E) : Prop :=
  (G.inc e).out.1 = (G.inc e).out.2

def hasLoop (G : MultiGraph V E) : Prop :=
  ∃ (e : E), G.isLoop e


noncomputable def neighbors (G : MultiGraph V E) (v : V) : Set V :=
  G.assignDi.outNeighbors v ∪ G.assignDi.inNeighbors v

lemma mem_neighbors_iff_mem_outNeighbors_or_mem_inNeighbors (G : MultiGraph V E) (v w : V) :
  w ∈ G.neighbors v ↔ w ∈ G.assignDi.outNeighbors v ∨ w ∈ G.assignDi.inNeighbors v := by
  rfl

lemma mem_neighbors_iff_adj_or_adj_comm (G : MultiGraph V E) (v w : V) :
  w ∈ G.neighbors v ↔ G.adj v w ∨ G.adj w v := by
  unfold neighbors adj MulDigraph.outNeighbors MulDigraph.inNeighbors MulDigraph.adj assignDi
  simp
  rw [← exists_or, ← exists_or]
  apply exists_congr
  intro e
  rw [Iff.comm, Sym2.eq_swap, or_self, or_comm]
  exact Sym2.eq_iff_out_eq_or_out_swap _ _ _
  done


noncomputable def degree (G : MultiGraph V E) (v : V) : ℕ :=
  G.assignDi.outDegree v + G.assignDi.inDegree v

lemma degree_eq_preimage_add_loops [Finite E] [DecidableEq E] (G : MultiGraph V E) (v : V) :
  G.degree v = (G.inc ⁻¹' { p : Sym2 V | v ∈ p }).ncard + (G.inc ⁻¹' { s(v, v) }).ncard := by
  unfold degree MulDigraph.outDegree MulDigraph.inDegree MulDigraph.outEdges MulDigraph.inEdges assignDi
  rw [← Set.ncard_union_add_ncard_inter]
  congr
  ·
    simp [← Set.setOf_or, @eq_comm _ _ v, @eq_comm _ _ v, ← Sym2.mem_iff, Prod.mk.eta, Quot.out_eq]
  ·
    ext e
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    nth_rewrite 1 [(by rfl : v = (v, v).fst)]
    nth_rewrite 3 [(by rfl : v = (v, v).snd)]
    rw [← Prod.eq_iff_fst_eq_snd_eq]
    constructor
    · -- 1.
      intro h
      rw [← h]
      simp
      done
    · -- 2.
      intro h
      rw [h]
      rcases Sym2.out_mk_eq_or_swap v v with h | h
      all_goals exact h
      done

/-################################ Subgraph ##################################-/

-- structure Minor (G : MultiGraph V E) where
--   E' : Set E
--   vmap : V →. V
--   -- some optional entries
--   V' : Set V := vmap.ran
--   vmap_ran : vmap.ran = V' := by rfl




end MultiGraph

namespace MultiGraph.Minor

-- def toMultiGraph {G : MultiGraph V E} (H : G.Minor) : MultiGraph H.V' H.E' :=
  -- { inc := λ e => H.vmap.image (G.inc e.1) }

-- From MultiGraph to Minor

-- def self (G : MultiGraph V E) : G.Minor where
--   E' := Set.univ
--   vmap := PFun.id V

-- def vertexSubgraph (G : MultiGraph V E) (S : Set V) : G.Minor where
--   E' := { e | ↑(G.inc e) ⊆ S }
--   vmap := PFun.res id S

-- def edgeSubgraph (G : MultiGraph V E) (E' : Set E) : G.Minor where
--   E' := E'
--   vmap := PFun.id V

-- def quotient (G : MultiGraph V E) (f : V → V) : G.Minor where
--   E' := Set.univ
--   vmap := PFun.comp f (PFun.id V)

-- noncomputable def vertexSubgraph (G : MultiGraph V E) (S : Set V) :
--   MultiGraph S { e : E // ∃ p' : Sym2 S, p'.map (·.1) = G.inc e} :=
--   { inc := λ ⟨ _, he ⟩ => Classical.choose he }

-- -- noncomputable def vertexSubgraph' (G : MultiGraph V E) (S : Set V) :
-- --   MultiGraph S { e : E // ↑(G.inc e) ⊆ S } where
-- --   inc := λ ⟨ e, he ⟩ => by
-- --     have h : ∀ v ∈ G.inc e, v ∈ S := by
-- --       intro v hv
-- --       exact he hv
-- --     rw [Sym2.subtype_iff_mem_sat] at h
-- --     exact Classical.choose h

-- def edgeSubgraph (G : MultiGraph V E) (E' : Set E) : MultiGraph V E' :=
--   { inc := λ e => G.inc e }

-- noncomputable def Subgraph (G : MultiGraph V E) (V' : Set V) (E' : Set E) :=
--   (G.vertexSubgraph V').edgeSubgraph { e | e.1 ∈ E' ∧ ↑(G.inc e) ⊆ V' }

-- -- def vertexSingleMerge [DecidableEq V] (G : MultiGraph V E) (v w : V) (hv : v ≠ w) :
-- --   MultiGraph {x : V // x ≠ w} E :=
-- --   { inc := λ e => (G.inc e).map (λ x : V => if hx : x = w then ⟨ v, hv ⟩ else ⟨ x, hx ⟩) }

-- def quotient {V' : Type*} (G : MultiGraph V E) (f : V → V') : MultiGraph V' E :=
--   { inc := λ e => (G.inc e).map f }

end MultiGraph.Minor

/-######################### Walks, Paths and Trails #########################-/

inductive MultiGraph.Walk {V E : Type u} (G : MultiGraph V E) : V → V → Type u
  | nil (v : V) : G.Walk v v
  | cons (v w u : V) (p : G.Walk v w) (e : E) (he : w ∈ G.inc e) : G.Walk v u

namespace MultiGraph.Walk

variable {V E : Type u} {G : MultiGraph V E}

def revVertices {v1 v2 : V} (W : G.Walk v1 v2) : List V :=
  match W with
  | nil v1 => [v1]
  | cons v1 _ v2 p _ _ => v2 :: p.revVertices

def vertices {v1 v2 : V} (W : G.Walk v1 v2) : List V :=
  W.revVertices.reverse

def revEdges {v1 v2 : V} (W : G.Walk v1 v2) : List E :=
  match W with
  | nil _ => []
  | cons _ _ _ p e _ => e :: p.revEdges

def edges {v1 v2 : V} (W : G.Walk v1 v2) : List E :=
  W.revEdges.reverse

def length {v1 v2 : V} (W : G.Walk v1 v2) : ℕ :=
  W.edges.length

def isPath {v1 v2 : V} (W : G.Walk v1 v2) : Prop :=
  W.vertices.Nodup

def isTrail {v1 v2 : V} (W : G.Walk v1 v2) : Prop :=
  W.edges.Nodup

def IsClosed {v1 v2 : V} (_ : G.Walk v1 v2) : Prop :=
  v1 = v2

def isCycle {v1 v2 : V} (W : G.Walk v1 v2) : Prop :=
  W.isPath ∧ W.IsClosed

def isTour {v1 v2 : V} (W : G.Walk v1 v2) : Prop :=
  W.isTrail ∧ W.IsClosed

-- noncomputable def asSubgraph [DecidableEq V] [DecidableEq E] {v1 v2 : V} (W : G.Walk v1 v2) :=
--   G.Subgraph W.vertices.toFinset W.edges.toFinset

-- def quotient [DecidableEq V] {v1 v2 : V} (W : G.Walk v1 v2) :
--   MultiGraph ({v | v ∉ W.vertices}.insert v1) E :=
--   G.quotient (fun v => if h : v ∈ W.vertices then ⟨ v1, Set.mem_insert v1 _⟩ else ⟨ v, by
--     apply Set.mem_insert_of_mem
--     simp [h]
--     ⟩ : V → ({v | v ∉ W.vertices}.insert v1))



end MultiGraph.Walk

/-########################## Connected and Strongly Connected ##########################-/



def MultiGraph.isConnected (G : MultiGraph V E) : Prop :=
  ∀ v w : V, ∃ (_ : G.Walk v w), true
