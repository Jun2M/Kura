import Mathlib
import Wagner.Sym2


@[ext]
structure MulDigraph (V : Type*) (E : Type*) :=
  (inc : E → (V × V))

namespace MulDigraph

variable {V : Type*} {E : Type*}


def adj (G : MulDigraph V E) (v w : V) : Prop :=
  ∃ (e : E), G.inc e = (v, w)

lemma adj_iff_exists_edge (G : MulDigraph V E) (v w : V) :
  G.adj v w ↔ ∃ (e : E), G.inc e = (v, w) := by
  rfl


def outNeighbors (G : MulDigraph V E) (v : V) : Set V :=
  { w | G.adj v w }

lemma outNeighbors_eq_setOf_adj (G : MulDigraph V E) (v : V) :
  G.outNeighbors v = { w | G.adj v w } := by
  rfl

lemma outNeighbors_eq_setOf_exists_edge (G : MulDigraph V E) (v : V) :
  G.outNeighbors v = { w | ∃ (e : E), G.inc e = (v, w) } := by
  simp_rw [outNeighbors_eq_setOf_adj, adj_iff_exists_edge]
  done

lemma mem_outNeighbors_iff_adj (G : MulDigraph V E) (v w : V) :
  w ∈ G.outNeighbors v ↔ G.adj v w := by
  rfl


def inNeighbors (G : MulDigraph V E) (v : V) : Set V :=
  { w | G.adj w v }

lemma inNeighbors_eq_setOf_adj (G : MulDigraph V E) (v : V) :
  G.inNeighbors v = { w | G.adj w v } := by
  rfl

lemma inNeighbors_eq_setOf_exists_edge (G : MulDigraph V E) (v : V) :
  G.inNeighbors v = { w | ∃ (e : E), G.inc e = (w, v) } := by
  simp_rw [inNeighbors_eq_setOf_adj, adj_iff_exists_edge]
  done

lemma mem_inNeighbors_iff_adj (G : MulDigraph V E) (v w : V) :
  w ∈ G.inNeighbors v ↔ G.adj w v := by
  rfl

lemma mem_outNeighbors_iff_mem_inNeighbors (G : MulDigraph V E) (v w : V) :
  w ∈ G.outNeighbors v ↔ v ∈ G.inNeighbors w := by
  rw [mem_outNeighbors_iff_adj, mem_inNeighbors_iff_adj]
  done


def outEdges (G : MulDigraph V E) (v : V) : Set E :=
  { e | (G.inc e).1 = v }

lemma outEdges_eq_setOf_incident_fst (G : MulDigraph V E) (v : V) :
  G.outEdges v = { e | (G.inc e).1 = v } := by
  rfl

lemma mem_outEdges_iff_incident_fst (G : MulDigraph V E) (v : V) (e : E) :
  e ∈ G.outEdges v ↔ (G.inc e).1 = v := by
  rfl

lemma mem_outEdges_of_fst (G : MulDigraph V E) (e : E) :
  e ∈ G.outEdges (G.inc e).1 := by
  rw [mem_outEdges_iff_incident_fst]


def inEdges (G : MulDigraph V E) (v : V) : Set E :=
  { e | (G.inc e).2 = v }

lemma inEdges_eq_setOf_incident_snd (G : MulDigraph V E) (v : V) :
  G.inEdges v = { e | (G.inc e).2 = v } := by
  rfl

lemma mem_inEdges_iff_incident_snd (G : MulDigraph V E) (v : V) (e : E) :
  e ∈ G.inEdges v ↔ (G.inc e).2 = v := by
  rfl

lemma mem_inEdges_of_snd (G : MulDigraph V E) (e : E) :
  e ∈ G.inEdges (G.inc e).2 := by
  rw [mem_inEdges_iff_incident_snd]


noncomputable def outDegree (G : MulDigraph V E) (v : V) : ℕ :=
  (G.outEdges v).ncard

lemma outDegree_eq_ncard_outEdges (G : MulDigraph V E) (v : V) :
  G.outDegree v = (G.outEdges v).ncard := by
  rfl


noncomputable def inDegree (G : MulDigraph V E) (v : V) : ℕ :=
  (G.inEdges v).ncard

lemma inDegree_eq_ncard_inEdges (G : MulDigraph V E) (v : V) :
  G.inDegree v = (G.inEdges v).ncard := by
  rfl


def sinks (G : MulDigraph V E) : Set V :=
  { v | G.outNeighbors v = ∅ }

lemma sinks_eq_setOf_outNeighbors_empty (G : MulDigraph V E) :
  G.sinks = { v | G.outNeighbors v = ∅ } := by
  rfl

lemma mem_sinks_iff_outNeighbors_empty (G : MulDigraph V E) (v : V) :
  v ∈ G.sinks ↔ G.outNeighbors v = ∅ := by
  rfl


def sources (G : MulDigraph V E) : Set V :=
  { v | G.inNeighbors v = ∅ }

lemma sources_eq_setOf_inNeighbors_empty (G : MulDigraph V E) :
  G.sources = { v | G.inNeighbors v = ∅ } := by
  rfl

lemma mem_sources_iff_inNeighbors_empty (G : MulDigraph V E) (v : V) :
  v ∈ G.sources ↔ G.inNeighbors v = ∅ := by
  rfl

end MulDigraph
