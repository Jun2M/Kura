import Kura.Searchable.Searchable
import Mathlib.Data.Fintype.Basic
import Kura.Graph.FullGraph

-- def subtypeOfFintype [Fintype α] (P : α → Prop) [DecidablePred P] : Fintype {v // P v} :=
--   Fintype.subtype (Finset.univ.filter P) (by simp)

namespace Graph
open edge
variable {V E : Type*} [LinearOrder V] [Fintype V] [Fintype E] (G : Graph V E) (u v : V)


instance Searchable_of_FintypeE [Fintype E] : Searchable G where
  outEdges v := Fintype.elems.filter (λ e => v ∈ G.startAt e)
  mem_outEdges v e := by
    rw [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun _ => Fintype.complete e
  inEdges v := Fintype.elems.filter (λ e => v ∈ G.finishAt e)
  mem_inEdges v e := by
    rw [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun _ => Fintype.complete e

theorem exist (G : Graph V E) [fullGraph G] : IsEmpty E ∨ Nonempty V := by
  by_cases hE : IsEmpty E
  · exact Or.inl hE
  · simp at hE
    choose v _ using exist_two_mem G (@Classical.ofNonempty _ hE)
    exact Or.inr (Nonempty.intro v)




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
