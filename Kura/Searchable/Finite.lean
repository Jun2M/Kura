import Kura.Searchable.Searchable
import Mathlib.Data.Fintype.Basic
import Kura.Graph.FullGraph

-- def subtypeOfFintype [Fintype α] (P : α → Prop) [DecidablePred P] : Fintype {v // P v} :=
--   Fintype.subtype (Finset.univ.filter P) (by simp)

namespace Graph
open edge
variable {V E : Type*} [LinearOrder V] [DecidableEq E] (G : Graph V E) (u v : V)


instance Searchable_of_FintypeE [Fintype E] : Searchable G where
  outEdges v := Fintype.elems.filter (λ e => v ∈ G.startAt e)
  mem_outEdges v e := by
    rw [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun _ => Fintype.complete e
  inEdges v := Fintype.elems.filter (λ e => v ∈ G.finishAt e)
  mem_inEdges v e := by
    rw [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun _ => Fintype.complete e

def maxDegree [Fintype V] [G.Searchable]: ℕ := Finset.univ.image (G.degree ·) |>.max |>.getD 0
macro "Δ(" G:term ")" : term => `(Graph.maxDegree $G)

def maxDegreeVerts [Fintype V] [G.Searchable]: Finset V :=
  Finset.univ.filter (λ v => G.degree v = G.maxDegree)

@[simp]
lemma mem_maxDegreeVerts [Fintype V] [G.Searchable] (v : V) :
    v ∈ G.maxDegreeVerts ↔ G.degree v = G.maxDegree := by
  simp only [maxDegreeVerts, Finset.mem_filter, Finset.mem_univ, true_and]

lemma maxDegreeVerts_nonempty [Fintype V] [G.Searchable] (hΔ : Δ(G) ≠ 0) :
    G.maxDegreeVerts.Nonempty := by
  unfold Graph.maxDegreeVerts Finset.Nonempty maxDegree
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have : Finset.univ.image (G.degree ·) |>.Nonempty := sorry
  obtain ⟨ n, hn ⟩ := Finset.max_of_nonempty this
  obtain ⟨ x, _, hx ⟩ := Finset.exists_max_image Finset.univ (G.degree ·) sorry
  use x
  sorry

def minDegree [Fintype V] [G.Searchable]: ℕ := Finset.univ.image (G.degree ·) |>.min |>.getD 0
macro "δ(" G:term ")" : term => `(Graph.minDegree $G)

def minDegreeVerts [Fintype V] [G.Searchable]: Finset V :=
  Finset.univ.filter (λ v => G.degree v = G.minDegree)

@[simp]
lemma mem_minDegreeVerts [Fintype V] [G.Searchable] (v : V) :
    v ∈ G.minDegreeVerts ↔ G.degree v = G.minDegree := by
  simp only [minDegreeVerts, Finset.mem_filter, Finset.mem_univ, true_and]

lemma minDegreeVerts_nonempty [Fintype V] [G.Searchable] (hδ : δ(G) ≠ 0) :
    G.minDegreeVerts.Nonempty := by sorry

end Graph


-- lemma degree_eq_edges_filter_startAt_card [fullGraph G] :
--   G.degree v = ((@Fintype.elems E _).filter (λ e => v ∈ G.startAt e)).card := by
--   -- simp [degree, outDegree, outNeighbors]
--   unfold degree outDegree outNeighbors Finset.card
--   apply Multiset.card_eq_card_of_rel (r := λ u e => G.goback? e u = some v)



--   match h : G.inc e with
--   | dir (a, b) =>
--     cases a <;> cases b <;> simp_all
--   | undir s => sorry


-- theorem handshake (G : Graph V E) [undirected G] : ∑ v, G.degree v = 2 * Fintype.card E := by
--   unfold degree outDegree outNeighbors
