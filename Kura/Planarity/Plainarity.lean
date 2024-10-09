import Mathlib.Data.Real.Basic
import Kura.Conn.Conn
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
  cycle_minEdgeCut (w : Cycle G) : H.minEdgeCut w.edges.toFinset
  minEdgeCut_cycle (S : Finset E) : G.minEdgeCut S → ∃ (w : Cycle H),
    S = w.edges.toFinset

class Planar_by_AbstractDual :=
  F : Type*
  FLinearOrder : LinearOrder F
  FNonempty : Nonempty F
  dualGraph : Graph F E
  dualGraphConn : dualGraph.connected
  isDual : AbstractDual G dualGraph

variable [Planar_by_AbstractDual G]

def Faces := Planar_by_AbstractDual.F (G := G)

instance instPlanar_by_AbstractDualFLinearOrder :
    LinearOrder (Planar_by_AbstractDual.F G) := Planar_by_AbstractDual.FLinearOrder
instance instPlanar_by_AbstractDualFacesLinearOrder :
    LinearOrder G.Faces := Planar_by_AbstractDual.FLinearOrder
def dualGraph := Planar_by_AbstractDual.dualGraph (G := G)
def duality : AbstractDual G (dualGraph G) := Planar_by_AbstractDual.isDual


instance instPlanar_by_AbstractDualFintype [Fintype E]:
    Fintype (Planar_by_AbstractDual.F G) := by
  sorry
instance instPlanar_by_AbstractDualFacesFintype [Fintype E]:
    Fintype G.Faces := instPlanar_by_AbstractDualFintype G



/--
Nonempty V is assumed because empty graph is connected but has 0 components
Hence, n - m + f = 1 not 2
Thought: Should we redefine connected graph to be the graphs with 1 compoent?
-/
theorem EulerFormula [Nonempty V] [Fintype V] [Fintype E] [G.connected]:
    Fintype.card V - Fintype.card E + Fintype.card G.Faces = 2 := by
<<<<<<< HEAD
  induction Fintype.card E with
  | zero => sorry
=======
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
>>>>>>> 9250d8074e1d8dc95f513794b9519172c9e34576


  | succ m => sorry



lemma bridge_iff_loop (G : Graph V E) [Planar_by_AbstractDual G] : (G.bridge e) ↔ G.dualGraph.isLoop e := by

  constructor <;> rintro h
  · have hmincut := G.bridge_is_minEdgeCut e h
    have  := G.duality.minEdgeCut_cycle {e} sorry
    obtain ⟨W, hW⟩ := this
    sorry

  · sorry

def IsFacialCycle (w : Cycle G) : Prop :=
  ∃ (f : G.Faces), w.edges.toFinset = G.dualGraph.isolatingEdgeCut f



end Graph
