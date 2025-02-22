import Kura.Graph.Defs

namespace Graph
variable {V W E F : Type*} {G : Graph V E}


structure Separation (G : Graph V E) where
  G₁ : Subgraph G
  G₂ : Subgraph G
  spec : G₁.Sₑ ∩ G₂.Sₑ = ∅

namespace Separation

noncomputable def order (Sep : Separation G) : ℕ := (Sep.G₁.Sᵥ ∩ Sep.G₂.Sᵥ).ncard



end Separation
end Graph
