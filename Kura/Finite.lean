import Kura.Subgraph
import Kura.Translation

namespace Graph
open edge
variable {V E : Type*} [DecidableEq V] [Fintype V] [Fintype E]

theorem exist (G : Graph V E) [fullGraph G] : IsEmpty E ∨ Nonempty V := by
  by_cases hE : IsEmpty E
  · exact Or.inl hE
  · simp at hE
    choose v _ using exist_mem G (@Classical.ofNonempty _ hE)
    exact Or.inr (Nonempty.intro v)

theorem handshake (G : Graph V E) [undirected G] : ∑ v, G.degree v = 2 * Fintype.card E := by
  unfold degree outDegree
