import Mathlib.Data.Real.Basic
import Kura.Conn.Conn
import Kura.Graph.Examples


namespace Graph
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] [LinearOrder E] [LinearOrder F]
  [Fintype V] [Fintype W] (G : Graph V E) [Undirected G]

-- structure PlainarEmbedding (G : Graph V E R) :=
--   (vertexEmbedding : V → ℝ × ℝ)
--   (edgeEmbedding : E → Set.Icc 0 1 → ℝ × ℝ)
--   (embedding_intersections : ∀ e₁ e₂, e₁ ≠ e₂ → ∀ t₂ ∈ Set.Icc 0 1,
--     ∀ t₂ ∈ Set.Icc 0 1, edgeEmbedding e₁ t₁ ≠ edgeEmbedding e₂ t₂)
--   (embedding_ends : ∀ e, edgeEmbedding e 0 = vertexEmbedding (G.inc e).val.fst ∧
--     edgeEmbedding e 1 = vertexEmbedding (G.ends e).snd)

structure AbstractDual (H : Graph W F) where
  eEquiv : E ≃ F
  cycle_minEdgeCut (w : Cycle G) : H.minEdgeCut (w.edges.map eEquiv.toFun).toFinset
  minEdgeCut_cycle (S : Finset E) : G.minEdgeCut S → ∃ (w : Cycle H),
    S = (w.edges.map eEquiv.invFun).toFinset

class Planar_by_AbstractDual :=
  F : Type*
  FLinearOrder : LinearOrder F
  Fintype : Fintype F
  FNonempty : Nonempty F
  dualGraph : Graph F E
  isDual : AbstractDual G dualGraph

variable [Planar_by_AbstractDual G]

def Faces := Planar_by_AbstractDual.F (G := G)

instance instPlanar_by_AbstractDualFLinearOrder :
    LinearOrder (Planar_by_AbstractDual.F G) := Planar_by_AbstractDual.FLinearOrder

instance instPlanar_by_AbstractDualFacesLinearOrder :
    LinearOrder G.Faces := Planar_by_AbstractDual.FLinearOrder

instance instPlanar_by_AbstractDualFintype :
    Fintype (Planar_by_AbstractDual.F G) := Planar_by_AbstractDual.Fintype

instance instPlanar_by_AbstractDualFacesFintype :
    Fintype G.Faces := Planar_by_AbstractDual.Fintype

def dualGraph :=
  Planar_by_AbstractDual.dualGraph (G := G)

def duality :
    AbstractDual G (dualGraph G) := Planar_by_AbstractDual.isDual

theorem EulerFormula [Nonempty V] [Fintype E] [G.connected]:
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
  G[w.vertices.toFinsetᶜ].connected



end Graph
