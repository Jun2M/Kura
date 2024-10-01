import Mathlib.Data.Real.Basic
import Kura.Conn.Conn
import Kura.Graph.Examples


namespace Graph
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] [LinearOrder E] [LinearOrder F]
  [Fintype V] [Fintype W] (G : Graph V E) [Undirected G]

-- structure PlainarEmbedding (G : Graph V E R) :=
--   (vertexEmbedding : V → ℝ × ℝ)
--   (edgeEmbedding : E → Set.Icc 0 1 → ℝ × ℝ)
--   (embedding_intersections : ∀ e₁ e₂, e₁ ≠ e₂ → ∀ t₂ ∈ Set.Icc 0 1,
--     ∀ t₂ ∈ Set.Icc 0 1, edgeEmbedding e₁ t₁ ≠ edgeEmbedding e₂ t₂)
--   (embedding_ends : ∀ e, edgeEmbedding e 0 = vertexEmbedding (G.inc e).val.fst ∧
--     edgeEmbedding e 1 = vertexEmbedding (G.ends e).snd)

structure AbstractDual (H : Graph W F) where
  eEquiv : E ≃ F
  cycle_minEdgeCut (w : Cycle G) : H.minEdgeCut (w.edges.map eEquiv.toFun).toFinset
  minEdgeCut_cycle (S : Finset F) : H.minEdgeCut S → ∃ (w : Cycle G),
    S = (w.edges.map eEquiv.toFun).toFinset

class Planar_by_AbstractDual : Prop :=
  exists_dual : ∃ (n m : ℕ) (H : Graph (Fin n) (Fin m)), Nonempty (AbstractDual G H)

def DualGraph [Planar_by_AbstractDual G] : Graph V E := by
  sorry

def DualGraph_AbstractDual [Planar_by_AbstractDual G] :
    AbstractDual G (DualGraph G) := by
  sorry

-- class Planar_by_AbstractDual :=
--   n : ℕ
--   m : ℕ
--   dualGraph : Graph (Fin n) (Fin m)
--   isDual : AbstractDual G dualGraph

def IsFacialCycle (w : Cycle G) : Prop :=
  G[w.vertices.toFinsetᶜ].connected

lemma CompleteGraph4_Planar : Planar_by_AbstractDual (CompleteGraph 4) where
  exists_dual := by
    refine ⟨4, 6, ?_, ?_⟩
    · exact {
        inc := λ e => edge.undir (List.finRange 4
          |>.sym2.filter (¬·.IsDiag) |>.get (e.cast (by rfl)))}

    · refine ⟨?_, ?_, ?_⟩
      · refine ⟨ (·.cast rfl), (·.cast rfl), ?_, ?_ ⟩
        <;> simp [Function.LeftInverse, Function.RightInverse]
      · intro c
        simp

        sorry
      sorry


end Graph
