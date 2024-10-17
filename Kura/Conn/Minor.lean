import Kura.Conn.Tree

namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E) (e : E) (u v w : V)


-- Merges to the start of the path
def Mp (G : Graph V E) [DecidableEq E] (P : G.Path) :
    Graph {v : V // v ∉ P.vertices.tail} {e : E // e ∉ P.edges} where
  inc e := G
    |>.Qs {v : V | v ∈ P.vertices.tail} P.start P.start_not_mem_vertices_tail
    |>.Es {e : E | e ∉ P.edges}
    |>.inc e

-- contraction by a rooted forest?

/-- definition not completed!!!!!!! -/
structure MinorOf (G : Graph V E) (H : Graph W F) [DecidableEq E] [DecidableEq F] where
  Ps : List (H.Path)

def MinorOf.refl (G : Graph V E) [DecidableEq E] : G.MinorOf G := sorry

def MinorOf.OfSubgraph (G : Graph V E) (H : Graph W F) [DecidableEq E] [DecidableEq F]
  (hGH : G ⊆ᴳ H) : G.MinorOf H := sorry
