import Kura.Graph.Translation
import Mathlib.Data.Fintype.Basic

-- def subtypeOfFintype [Fintype α] (P : α → Prop) [DecidablePred P] : Fintype {v // P v} :=
--   Fintype.subtype (Finset.univ.filter P) (by simp)

namespace Graph
open edge
variable {V E : Type*} [LinearOrder V] [Fintype V] [Fintype E] (G : Graph V E) (u v : V)

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
