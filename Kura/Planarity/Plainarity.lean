import Kura.Connectivity.nConn
import Kura.Examples.Conn
import Kura.Connectivity.Minor


namespace Graph
variable {V E F : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq F] (G : Graph V E)
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

class Planar_by_AbstractDual where
  F : Type*
  FDecidableEq : DecidableEq F
  dualGraph : Graph F E
  dualGraphUndir : dualGraph.Undirected
  dualGraphConn : dualGraph.connected
  isDual : AbstractDual G dualGraph

variable [Planar_by_AbstractDual G]

def Faces := Planar_by_AbstractDual.F (G := G)

instance instPlanar_by_AbstractDualFDecidableEq :
    DecidableEq (Planar_by_AbstractDual.F G) := Planar_by_AbstractDual.FDecidableEq
instance instPlanar_by_AbstractDualFacesDecidableEq :
    DecidableEq G.Faces := Planar_by_AbstractDual.FDecidableEq
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
instance instPlanar_by_AbstractDualFintypeEdges [Fintype G.Edges]:
    Fintype (Planar_by_AbstractDual.F G) := by
  sorry
instance instPlanar_by_AbstractDualFacesFintypeEdges [Fintype G.Edges]:
    Fintype G.Faces := instPlanar_by_AbstractDualFintypeEdges G

lemma bridge_iff_loop [G.connected] :
    G.bridge e ↔ G.dualGraph.isLoop e := by
  constructor <;> rintro h
  · have hmincut := G.bridge_minEdgeCut e h
    have  := (G.duality.minEdgeCut_cycle {e}).mp hmincut
    obtain ⟨W, hW⟩ := this
    have : W.edges = [e] := sorry
    exact W.isLoop_of_edges_singleton e this
  · obtain C : G.dualGraph.Cycle := Cycle.ofLoop G.dualGraph e h
    have hmincut := (G.duality.minEdgeCut_cycle C.edges.toFinset).mpr ⟨C, rfl⟩
    have : C.edges.toFinset = {e} := sorry
    simp only [this, Finset.coe_singleton] at hmincut
    exact ⟨ by assumption, edgeCut_of_minEdgeCut {e} hmincut ⟩


instance doubleDual [Fintype V] [Nonempty V] [G.nConnected 3] :
    Planar_by_AbstractDual (dualGraph G) where
  F := V
  FDecidableEq := by assumption
  dualGraph := G
  dualGraphUndir := by assumption
  dualGraphConn := G.connected_of_nConnected 3
  isDual := sorry

instance instEdgelessGraphPlanar_by_AbstractDual (n : ℕ) :
    Planar_by_AbstractDual (EdgelessGraph n) where
  F := Fin 1
  FDecidableEq := by infer_instance
  dualGraph := EdgelessGraph 1
  dualGraphUndir := by infer_instance
  dualGraphConn := by have : Fact (1 < 2) := Fact.mk (by omega); infer_instance
  isDual := by
    refine ⟨λ S => ⟨λ h => ?_, λ ⟨c, _hc⟩ => ?_⟩⟩
    · have : S = ∅ := S.eq_empty_of_isEmpty
      subst this
      exfalso
      exact empty_not_minEdgeCut h
    · have : c.edges = [] := List.eq_nil_of_IsEmpty c.edges
      exfalso
      exact c.eNonempty this

instance instPlanar_by_AbstractDualOfEdgeIsEmpty [IsEmpty E] :
    Planar_by_AbstractDual G where
  F := Fin 1
  FDecidableEq := by infer_instance
  dualGraph := {inc := (IsEmpty.elim (by assumption) ·)}
  dualGraphUndir := by sorry
  dualGraphConn := by
    refine ⟨λ u v => ?_⟩
    have := Subsingleton.allEq u v
    subst u
    apply conn.refl
  isDual := by
    refine ⟨λ S => ⟨λ h => ?_, λ ⟨c, hc⟩ => ?_⟩⟩
    · have : S = ∅ := S.eq_empty_of_isEmpty
      subst this
      exfalso
      exact empty_not_minEdgeCut h
    · have : c.edges = [] := List.eq_nil_of_IsEmpty c.edges
      exfalso
      exact c.eNonempty this

-- The following definitions should be sufficient to show that any planar graph is planar by
-- abstract dual.
def CycleGraph.Planar_by_AbstractDual (n : ℕ) (hn : 1 < n) :
    Planar_by_AbstractDual (CycleGraph n hn) where
  F := Fin 2
  FDecidableEq := by infer_instance
  dualGraph :=( {inc := fun e ↦ edge.undir s(0, 1)} : Graph (Fin 2) (Fin n))
  dualGraphUndir := sorry
  dualGraphConn := sorry
  isDual := sorry

def MinorOf.Planar_by_AbstractDual {H : Graph F E} (M : G.MinorOf H) :
    Planar_by_AbstractDual H := sorry

def MergeOnMultualSubgraph.Planar_by_AbstractDual {H : Graph F E} (A₁ : CompleteGraph 2 ⊆ᴳ G)
    (A₂ : CompleteGraph 2 ⊆ᴳ H) : Planar_by_AbstractDual (MergeOnMultualSubgraph G H A₁ A₂) := sorry

def inSameFace (u v : V) : Prop := ∃ (f : G.Faces) (e1 e2 : G.Edges), u ∈ G.endAt e1 ∧
  v ∈ G.endAt e2 ∧ f ∈ G.dualGraph.endAt e1 ∧ f ∈ G.dualGraph.endAt e2

def addUndirEdge.Planar_by_AbstractDual {u v : V} (h : G.inSameFace u v) :
    Planar_by_AbstractDual (G.addUndirEdge s(u, v)) := sorry


/-
From here on, lets not appeal to the definition of planarity by abstract dual
-/



end Graph
