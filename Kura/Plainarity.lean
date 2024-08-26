import Mathlib.Data.Real.Basic
import Kura.Defs


namespace Graph
variable {αᵥ αₑ : Type u} {R : αᵥ → αᵥ → Prop} [DecidableEq αᵥ]
  [DecidableRel R] [IsAntisymm αᵥ R] [IsTotal αᵥ R]

structure PlainarEmbedding (G : Graph αᵥ αₑ R) :=
  (vertexEmbedding : αᵥ → ℝ × ℝ)
  (edgeEmbedding : αₑ → Set.Icc 0 1 → ℝ × ℝ)
  (embedding_intersections : ∀ e₁ e₂, e₁ ≠ e₂ → ∀ t₂ ∈ Set.Icc 0 1,
    ∀ t₂ ∈ Set.Icc 0 1, edgeEmbedding e₁ t₁ ≠ edgeEmbedding e₂ t₂)
  (embedding_ends : ∀ e, edgeEmbedding e 0 = vertexEmbedding (G.inc e).val.fst ∧
    edgeEmbedding e 1 = vertexEmbedding (G.ends e).snd)



end Graph
