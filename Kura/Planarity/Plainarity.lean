import Mathlib.Data.Real.Basic
import Kura.Conn.nConn
import Kura.Graph.Examples


namespace Graph
variable {V E F : Type*} [LinearOrder V] [LinearOrder E] [LinearOrder F] (G : Graph V E)
  [Undirected G]

-- structure PlainarEmbedding (G : Graph V E R) :=
--   (vertexEmbedding : V → ℝ × ℝ)
--   (edgeEmbedding : E → Set.Icc 0 1 → ℝ × ℝ)
--   (embedding_intersections : ∀ e₁ e₂, e₁ ≠ e₂ → ∀ t₂ ∈ Set.Icc 0 1,
--     ∀ t₂ ∈ Set.Icc 0 1, edgeEmbedding e₁ t₁ ≠ edgeEmbedding e₂ t₂)
--   (embedding_ends : ∀ e, edgeEmbedding e 0 = vertexEmbedding (G.inc e).val.fst ∧
--     edgeEmbedding e 1 = vertexEmbedding (G.ends e).snd)

structure AbstractDual (H : Graph F E) where
  minEdgeCut_cycle (S : Set E) : G.minEdgeCut S ↔ ∃ (w : Cycle H), S = w.edges.toFinset

class Planar_by_AbstractDual :=
  F : Type*
  FLinearOrder : LinearOrder F
  FNonempty : Nonempty F
  dualGraph : Graph F E
  dualGraphUndir : dualGraph.Undirected
  dualGraphConn : dualGraph.connected
  isDual : AbstractDual G dualGraph

variable [Planar_by_AbstractDual G]

def Faces := Planar_by_AbstractDual.F (G := G)

instance instPlanar_by_AbstractDualFLinearOrder :
    LinearOrder (Planar_by_AbstractDual.F G) := Planar_by_AbstractDual.FLinearOrder
instance instPlanar_by_AbstractDualFacesLinearOrder :
    LinearOrder G.Faces := Planar_by_AbstractDual.FLinearOrder
def dualGraph := Planar_by_AbstractDual.dualGraph (G := G)
instance instPlanar_by_AbstractDualdualGraphUndirected :
    Undirected G.dualGraph := Planar_by_AbstractDual.dualGraphUndir
instance instPlanar_by_AbstractDualdualGraphConnected :
    connected G.dualGraph := Planar_by_AbstractDual.dualGraphConn
def duality : AbstractDual G (dualGraph G) := Planar_by_AbstractDual.isDual


instance instPlanar_by_AbstractDualFintype [Fintype E]:
    Fintype (Planar_by_AbstractDual.F G) := by
  sorry
instance instPlanar_by_AbstractDualFacesFintype [Fintype E]:
    Fintype G.Faces := instPlanar_by_AbstractDualFintype G


lemma bridge_iff_loop [Planar_by_AbstractDual G] :
    G.bridge e ↔ G.dualGraph.isLoop e := by
  constructor <;> rintro h
  · have hmincut := G.bridge_is_minEdgeCut e h
    have  := (G.duality.minEdgeCut_cycle {e}).mp hmincut
    obtain ⟨W, hW⟩ := this
    have : W.edges = [e] := sorry
    exact W.isLoop_of_edges_singleton G.dualGraph e this
  · let v := (G.dualGraph.get e).inf
    obtain C : G.dualGraph.Cycle := Cycle.ofLoop G.dualGraph e h

    have hmincut := (G.duality.minEdgeCut_cycle C.edges.toFinset).mpr ⟨C, rfl⟩
    have : C.edges.toFinset = {e} := sorry
    simp only [this, Finset.coe_singleton] at hmincut
    exact edgeCut_of_minEdgeCut G {e} hmincut


instance doubleDual [Fintype V] [Nonempty V] [Planar_by_AbstractDual G] [G.nConnected 3] :
    Planar_by_AbstractDual (dualGraph G) where
  F := V
  FLinearOrder := by assumption
  FNonempty := by assumption
  dualGraph := G
  dualGraphUndir := by assumption
  dualGraphConn := G.connected_of_nConnected 3
  isDual := sorry



/--
Nonempty V is assumed because empty graph is connected but has 0 components
Hence, n - m + f = 1 not 2
Thought: Should we redefine connected graph to be the graphs with 1 compoent?
-/
theorem EulerFormula [Nonempty V] [Fintype V] [Fintype E] [G.connected]:
    Fintype.card V - Fintype.card E + Fintype.card G.Faces = 2 := by
  have := VSubsingletonofConnectedEcardZero G
  revert this
  induction Fintype.card E  with
  | zero =>
    rintro h
    simp only [true_implies] at h
    have hle1: Fintype.card V ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr h
    have h0lt: Fintype.card V > 0 := Fintype.card_pos
    have : Fintype.card V = 1 := Eq.symm (Nat.le_antisymm h0lt hle1)
    rw [this]; clear h hle1 h0lt this

    sorry


  | succ m => sorry


def IsFacialCycle (w : Cycle G) : Prop :=
  ∃ (f : G.Faces), w.edges.toFinset = G.dualGraph.isolatingEdgeCut f



end Graph
