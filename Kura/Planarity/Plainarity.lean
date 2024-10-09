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

theorem EulerFormula [Fintype E] [G.connected]:
    Fintype.card V - Fintype.card E + Fintype.card G.Faces = 2 := by
  induction Fintype.card E with
  | zero => sorry


  | succ m => sorry



lemma bridge_iff_loop (G : Graph V E) [Planar_by_AbstractDual G] : (G.bridge e) ↔ G.dualGraph.isLoop e := by

  constructor <;> rintro h
  · have hmincut := G.bridge_is_minEdgeCut e h
    have  := G.duality.minEdgeCut_cycle {e} sorry
    obtain ⟨W, hW⟩ := this
    sorry

  · sorry

def IsFacialCycle (w : Cycle G) : Prop :=
  G[w.vertices.toFinsetᶜ].connected



end Graph
