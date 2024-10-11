import Kura.Conn.Conn
import Kura.Conn.closedWalk


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] [DecidableEq E] (G : Graph V E)

class nEdgeConnected (n : ℕ) : Prop :=
  all_conn : ∀ u v : V, conn G u v
  no_small_cut : ∀ S : Finset E, S.card < n → ¬ G.edgeCut S

class nConnected [fullGraph G] (n : ℕ) : Prop where
  h : ∀ S : Finset V, S.card ≤ n → G[Sᶜ]ᴳ.connected

lemma conn_le_minDegree [Fintype V] [fullGraph G] [Searchable G] (k : ℕ) [nConnected G k] (v : V) :
    k ≤ G.minDegree := by
  sorry

def isolatingCut [nConnected G 2]
