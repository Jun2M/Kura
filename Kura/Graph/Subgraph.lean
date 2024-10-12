import Kura.Conn.Walk


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W]


-- one op?
def Vs (G : Graph V E) (S : Set V) [DecidablePred (· ∈ S)] : Graph S {e // G.all e (· ∈ S) } where
  inc e :=
    let ⟨e, he⟩ := e
    edge.pmap Subtype.mk (G.inc e) (by
    intro v hv
    simp only [all, all_iff, decide_eq_true_eq] at he
    exact he v hv)

macro G:term "[" S:term "]ᴳ" : term => `(Graph.Vs $G $S)

def Es (G : Graph V E) (S : Set E) [DecidablePred (· ∈ S)] : Graph V S where
  inc := (G.inc ·.val)

macro G:term "{" S:term "}ᴳ" : term => `(Graph.Es $G $S)


def Qs (G : Graph V E) (S : Set V) [DecidablePred (· ∈ S)] (v : V) (hv : v ∉ S) :
  Graph (Sᶜ:Set _) E where
  inc e := G.inc e
    |>.map (fun u => if u ∈ S then v else u)
    |>.pmap Subtype.mk (fun w hw => by
      simp only [mem_map_iff] at hw
      obtain ⟨u, _hu, rfl⟩ := hw
      split
      · exact hv
      · assumption)

-- Merges to the start of the path
def Ms (G : Graph V E) [DecidableEq E] (P : G.Path) :
    Graph {v : V // v ∉ P.vertices.tail} {e : E // e ∉ P.edges} where
  inc e := G
    |>.Qs {v : V | v ∈ P.vertices.tail} P.start P.start_not_mem_vertices_tail
    |>.Es {e : E | e ∉ P.edges}
    |>.inc e

-- contraction by a rooted tree?
