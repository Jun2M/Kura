import Mathlib.Data.Real.Basic
import Kura.Subgraph


namespace Graph
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] [LinearOrder E] [LinearOrder F] [Fintype V] [Fintype W]

-- structure PlainarEmbedding (G : Graph V E R) :=
--   (vertexEmbedding : V → ℝ × ℝ)
--   (edgeEmbedding : E → Set.Icc 0 1 → ℝ × ℝ)
--   (embedding_intersections : ∀ e₁ e₂, e₁ ≠ e₂ → ∀ t₂ ∈ Set.Icc 0 1,
--     ∀ t₂ ∈ Set.Icc 0 1, edgeEmbedding e₁ t₁ ≠ edgeEmbedding e₂ t₂)
--   (embedding_ends : ∀ e, edgeEmbedding e 0 = vertexEmbedding (G.inc e).val.fst ∧
--     edgeEmbedding e 1 = vertexEmbedding (G.ends e).snd)

structure AbstractDual (G : Graph V E) (H : Graph W F) where
  eEquiv : E ≃ F
  cycle_minEdgeCut (w : Cycle G) : H.minEdgeCut (w.edges.map eEquiv.toFun).toFinset
  minEdgeCut_cycle (S : Finset F) : H.minEdgeCut S → ∃ (w : Cycle G),
    S = (w.edges.map eEquiv.toFun).toFinset

class Planar_by_AbstractDual (G : Graph V E) : Prop :=
  exists_dual : ∃ (n m : ℕ) (H : Graph (Fin n) (Fin m)), Nonempty (AbstractDual G H)

def DualGraph (G : Graph V E) [Planar_by_AbstractDual G] : Graph V E := by
  sorry

def DualGraph_AbstractDual (G : Graph V E) [Planar_by_AbstractDual G] :
    AbstractDual G (DualGraph G) := by
  sorry

-- class Planar_by_AbstractDual (G : Graph V E) :=
--   n : ℕ
--   m : ℕ
--   dualGraph : Graph (Fin n) (Fin m)
--   isDual : AbstractDual G dualGraph


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

lemma CompleteGraph5_not_Planar :
    ¬ Planar_by_AbstractDual (CompleteGraph 5) := by
  intro h
  obtain ⟨H, fE, hcm, hmc⟩ := h.exists_dual
  sorry

lemma CompleteBipGraph33_not_Planar :
    ¬ Planar_by_AbstractDual (CompleteBipGraph 3 3) := by
  sorry

theorem KuraCore (G : Graph V E) (hG3conn : )

end Graph
