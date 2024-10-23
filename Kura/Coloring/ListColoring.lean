import Kura.Graph.Bipartite
import Kura.Graph.Searchable

namespace Graph
open edge Sym2
variable {V E W F : Type*} [LinearOrder V] [Fintype V] [LinearOrder E] [Fintype E] [LinearOrder F]
  [Fintype F] [LinearOrder W] [Fintype W]


def IsListColoring (G : Graph V E) [Simple G] [Searchable G] (l : V → List ℕ) (c : V → ℕ) : Prop :=
  ∀ v : V, c v ∈ l v

instance instListColoringExistDeciable (G : Graph V E) [Simple G] [Searchable G] (l : V → List ℕ) :
    Decidable (∃ c, IsListColoring G l c) :=
  sorry

def ListChromaticIndex (G : Graph V E) [Simple G] [Searchable G] : ℕ :=
  @Nat.find (λ n : ℕ => ∀ l : V → List ℕ, (∀ v, n ≤ (l v).length) → ∃ c, IsListColoring G l c) sorry (by
    use Fintype.card V
    sorry)

