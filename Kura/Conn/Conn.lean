import Kura.Conn.Walk
import Kura.Graph.Subgraph


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E)

def Acyclic (G : Graph V E) : Prop := IsEmpty (Cycle G)

def conn (G : Graph V E) (u v : V) : Prop := ∃ w : Walk G, w.start = u ∧ w.finish = v

class connected (G : Graph V E) : Prop :=
  all_conn : ∀ u v : V, conn G u v

def componentOf (G : Graph V E) (v : V) : Set V := {u | G.conn u v}

def edgeCut (G : Graph V E) (S : Finset E) : Prop :=
  ∃ u v, G.conn u v ∧ ∀ w : Walk G, w.start = u ∧ w.finish = v → ∃ e ∈ S, e ∈ w.edges

def bridge (G : Graph V E) (e : E) : Prop := G.edgeCut {e}

def minEdgeCut (G : Graph V E) (S : Finset E) : Prop :=
  Minimal (G.edgeCut ·) S

class NEdgeConnected (G : Graph V E) (n : ℕ) : Prop :=
  all_conn : ∀ u v : V, conn G u v
  no_small_cut : ∀ S : Finset E, S.card < n → ¬ G.edgeCut S

def ball (u : V) (n : ℕ) : Set V :=
  {v | ∃ w : Walk G, w.start = u ∧ w.length ≤ n ∧ w.finish = v}

class NConnected (G : Graph V E) [Fintype V] [fullGraph G] (n : ℕ) : Prop where
  h : ∀ S : Finset V, S.card ≤ n → G[Sᶜ].connected
