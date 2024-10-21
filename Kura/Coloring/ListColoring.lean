import Kura.Graph.Bipartite

namespace Graph
open edge Sym2
variable {V W E F : Type*} [LinearOrder V] [Fintype V] [LinearOrder W] [Fintype W] [LinearOrder E]
  [Fintype E] [LinearOrder F] [Fintype F]

structure ListColoring (G : Graph V E) (c : V → ℕ)
