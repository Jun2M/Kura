import Kura.Conn.Walk
import Kura.Graph.Subgraph


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E)

def Acyclic : Prop := IsEmpty (Cycle G)

def conn (u v : V) : Prop := ∃ w : Walk G, w.start = u ∧ w.finish = v

class connected : Prop :=
  all_conn : ∀ u v : V, conn G u v

def componentOf (v : V) : Set V := {u | G.conn u v}

def edgeCut (S : Set E) : Prop :=
  ∃ u v, G.conn u v ∧ ∀ w : Walk G, w.start = u ∧ w.finish = v → ∃ e ∈ S, e ∈ w.edges

def bridge (e : E) : Prop := G.edgeCut {e}

def minEdgeCut (S : Set E) : Prop :=
  Minimal (G.edgeCut ·) S

def isolatingEdgeCut (v : V) : Set E := {e | v ∈ G.endAt e}

lemma isolatingEdgeCut_is_edgeCut (v : V) [Nontrivial V] : G.edgeCut (G.isolatingEdgeCut v) := by
  simp [isolatingEdgeCut, edgeCut]
  obtain ⟨a, b, ha⟩ := Nontrivial.exists_pair_ne (α := V)
  sorry



class NEdgeConnected (n : ℕ) : Prop :=
  all_conn : ∀ u v : V, conn G u v
  no_small_cut : ∀ S : Finset E, S.card < n → ¬ G.edgeCut S

def ball (u : V) (n : ℕ) : Set V :=
  {v | ∃ w : Walk G, w.start = u ∧ w.length ≤ n ∧ w.finish = v}

class NConnected [Fintype V] [fullGraph G] (n : ℕ) : Prop where
  h : ∀ S : Finset V, S.card ≤ n → G[Sᶜ].connected
