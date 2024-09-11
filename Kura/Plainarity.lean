import Mathlib.Data.Real.Basic
import Kura.Defs


namespace Graph
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq F]
  -- {R : V → V → Prop} [DecidableRel R] [IsAntisymm V R] [IsTotal V R]

-- structure PlainarEmbedding (G : Graph V E R) :=
--   (vertexEmbedding : V → ℝ × ℝ)
--   (edgeEmbedding : E → Set.Icc 0 1 → ℝ × ℝ)
--   (embedding_intersections : ∀ e₁ e₂, e₁ ≠ e₂ → ∀ t₂ ∈ Set.Icc 0 1,
--     ∀ t₂ ∈ Set.Icc 0 1, edgeEmbedding e₁ t₁ ≠ edgeEmbedding e₂ t₂)
--   (embedding_ends : ∀ e, edgeEmbedding e 0 = vertexEmbedding (G.inc e).val.fst ∧
--     edgeEmbedding e 1 = vertexEmbedding (G.ends e).snd)

structure AbstractDual (G : Graph V E) (H : Graph W F) where
  eEquiv : E ≃ F
  cycle_mincut : ∀ (w : Walk G), w.Cycle → H.mincut (w.edges.map eEquiv.toFun).toFinset
  mincut_cycle : ∀ (S : Finset F), H.mincut S → ∃ (w : Walk G), w.Cycle ∧
    S = (w.edges.map eEquiv.toFun).toFinset

class Planar_by_AbstractDual (G : Graph V E) : Prop :=
  exists_dual : ∃ (W F : Type*) (_ : DecidableEq W) (_ : DecidableEq F) (H : Graph W F),
    Nonempty (AbstractDual G H)



end Graph
