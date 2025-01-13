import Kura.Connectivity.Conn
import Kura.Connectivity.closedWalk


namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq E] (G : Graph V E)

class nEdgeConnected (n : ℕ) : Prop where
  all_conn : ∀ u v : V, conn G u v
  no_small_cut : ∀ S : Finset E, S.card < n → ¬ G.edgeCut S

class nConnected [Fintype V] [fullGraph G] (n : ℕ) : Prop where
  h : ∀ S : Finset V, S.card ≤ n → G[Sᶜ]ᴳ.connected

variable [Fintype V] [fullGraph G]

lemma cnt_le_minDegree [Searchable G] (k : ℕ) [nConnected G k] (v : V) : k ≤ G.minDegree := by
  sorry

lemma maxDegree_le_cnt [Searchable G] (k : ℕ) [nConnected G k] : G.maxDegree ≤ k := by
  sorry

instance instConnected [nConnected G 0] : connected G := by
  sorry

lemma connected_of_nConnected (k : ℕ) [nConnected G k] : connected G := by
  sorry

lemma nConnected_downward_closed (k : ℕ) [nConnected G k] (k' : ℕ) (h : k' ≤ k) :
    nConnected G k' := by
  sorry

end Graph
