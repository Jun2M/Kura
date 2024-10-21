import Kura.Conn.nConn
import Kura.Examples.Conn
import Kura.Conn.Minor


namespace Graph
variable {V E F : Type*} [LinearOrder V] [DecidableEq E] [LinearOrder F] (G : Graph V E)
  [Undirected G]

-- structure PlainarEmbedding (G : Graph V E R) :=
--   (vertexEmbedding : V → ℝ × ℝ)
--   (edgeEmbedding : E → Set.Icc 0 1 → ℝ × ℝ)
--   (embedding_intersections : ∀ e₁ e₂, e₁ ≠ e₂ → ∀ t₂ ∈ Set.Icc 0 1,
--     ∀ t₂ ∈ Set.Icc 0 1, edgeEmbedding e₁ t₁ ≠ edgeEmbedding e₂ t₂)
--   (embedding_ends : ∀ e, edgeEmbedding e 0 = vertexEmbedding (G.inc e).val.fst ∧
--     edgeEmbedding e 1 = vertexEmbedding (G.ends e).snd)

structure AbstractDual (H : Graph F E) where
  minEdgeCut_cycle (S : Finset E) : G.minEdgeCut S ↔ ∃ (w : Cycle H), S = w.edges.toFinset

class Planar_by_AbstractDual :=
  F : Type*
  FLinearOrder : LinearOrder F
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


lemma bridge_iff_loop [G.connected] [Planar_by_AbstractDual G] :
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
    exact ⟨ by assumption, edgeCut_of_minEdgeCut G {e} hmincut ⟩


instance doubleDual [Fintype V] [Nonempty V] [Planar_by_AbstractDual G] [G.nConnected 3] :
    Planar_by_AbstractDual (dualGraph G) where
  F := V
  FLinearOrder := by assumption
  dualGraph := G
  dualGraphUndir := by assumption
  dualGraphConn := G.connected_of_nConnected 3
  isDual := sorry

instance instEdgelessGraphPlanar_by_AbstractDual (n : ℕ) :
    Planar_by_AbstractDual (EdgelessGraph n) where
  F := Fin 1
  FLinearOrder := by infer_instance
  dualGraph := EdgelessGraph 1
  dualGraphUndir := by infer_instance
  dualGraphConn := by have : Fact (1 < 2) := Fact.mk (by omega); infer_instance
  isDual := by
    refine ⟨λ S => ⟨λ h => ?_, λ ⟨c, _hc⟩ => ?_⟩⟩
    · have : S = ∅ := S.eq_empty_of_isEmpty
      subst this
      exfalso
      exact empty_not_minEdgeCut _ h
    · have : c.edges = [] := List.eq_nil_of_IsEmpty c.edges
      exfalso
      exact c.eNonempty this

instance instPlanar_by_AbstractDualOfEdgeIsEmpty [IsEmpty E] :
    Planar_by_AbstractDual G where
  F := Fin 1
  FLinearOrder := by infer_instance
  dualGraph := {inc := (IsEmpty.elim (by assumption) ·)}
  dualGraphUndir := by sorry
  dualGraphConn := by
    refine ⟨λ u v => ?_⟩
    have := Subsingleton.allEq u v
    subst u
    apply conn_refl
  isDual := by
    refine ⟨λ S => ⟨λ h => ?_, λ ⟨c, hc⟩ => ?_⟩⟩
    · have : S = ∅ := S.eq_empty_of_isEmpty
      subst this
      exfalso
      exact empty_not_minEdgeCut _ h
    · have : c.edges = [] := List.eq_nil_of_IsEmpty c.edges
      exfalso
      exact c.eNonempty this

lemma Faces_card_eq_one_of_no_edges [IsEmpty E] :
    @Fintype.card G.Faces (by have := Fintype.ofIsEmpty (α := E); infer_instance) = 1 := by
  sorry

lemma EulerFormula_aux [Nonempty V] [Fintype V] [Fintype E]:
    Fintype.card E = n →
      Fintype.card V + Fintype.card G.Faces - Fintype.card E = 1 + NumberOfComponents G := by
  have hVpos : Fintype.card V > 0 := Fintype.card_pos
  induction n generalizing E with
  | zero =>
    intro hE0
    have hE := (Fintype.card_eq_zero_iff (α := E)).mp hE0
    have hV := NumberOfComponents_eq_card_V G
    rw [hV, hE0, Faces_card_eq_one_of_no_edges]
    omega
  | succ m ih =>
    intro hEcard
    have : Nonempty E := by
      rw [← Fintype.card_pos_iff]
      omega
    obtain e : E := Classical.choice this
    let G' := G{{e}ᶜ}ᴳ
    have hG'Undir : G'.Undirected := by sorry
    have hG'Planar : Planar_by_AbstractDual G' := by sorry
    -- let hG'SubgraphOf : G'.SubgraphOf G :=
    specialize @ih ({e}ᶜ : Set E) _ G' hG'Undir hG'Planar _ (by simp only [compl,
      Set.mem_singleton_iff, Set.coe_setOf, Fintype.card_subtype_compl, hEcard,
      Fintype.card_ofSubsingleton, add_tsub_cancel_right])
    simp only [compl, Set.coe_setOf, Set.mem_setOf_eq, Set.mem_singleton_iff,
      Fintype.card_subtype_compl, hEcard, Fintype.card_ofSubsingleton, add_tsub_cancel_right] at ih
    rw [Nat.sub_toss_eq' (by omega), Nat.add_toss_eq' hVpos] at ih ⊢
    rw [ih]; clear ih

    suffices h: G'.NumberOfComponents + Fintype.card G.Faces =
      1 + G.NumberOfComponents + Fintype.card G'.Faces by
      omega

    obtain u := G.v1 e
    obtain v := G.v2 e
    by_cases hG'conn : G'.conn u v
    · have hNC : G'.NumberOfComponents = G.NumberOfComponents := by
        unfold Graph.NumberOfComponents
        have hconnEq : G'.connSetoid = G.connSetoid := by
          unfold Graph.connSetoid
          ext x y
          unfold Setoid.Rel
          simp only
          constructor
          · intro h
            have := h.SubgraphOf (Es_subgraph G {e}ᶜ)
            simpa only [Es_subgraph_fᵥ, id_eq] using this
          · intro h
            induction h with
            | refl => exact conn_refl G' x
            | tail h1 h2 IH => sorry
        have := hconnEq
        apply_fun Quotient at hconnEq
        have : Fintype (Quotient G'.connSetoid) :=
          @Quotient.fintype _ _  G'.connSetoid (by rintro u v; apply Relation.ReflTransGenDeciable)
        have : Fintype (Quotient G.connSetoid) :=
          @Quotient.fintype _ _ G.connSetoid (by rintro u v; apply Relation.ReflTransGenDeciable)
        apply_fun Fintype.card at hconnEq
        convert hconnEq
      have hF : Fintype.card G'.Faces + 1 = Fintype.card G.Faces := by
        sorry
      omega
    · have hNC : G'.NumberOfComponents = G.NumberOfComponents + 1 := by
        sorry
      have hF : Fintype.card G'.Faces = Fintype.card G.Faces := by
        sorry
      omega

theorem EulerFormula [Nonempty V] [Fintype V] [Fintype E]:
    Fintype.card V + Fintype.card G.Faces - Fintype.card E = 1 + NumberOfComponents G :=
  EulerFormula_aux G rfl

theorem EulerFormula_of_connected [Nonempty V] [Fintype V] [Fintype E] [G.connected] :
    Fintype.card V + Fintype.card G.Faces - Fintype.card E = 2 := by
  rw [EulerFormula G, NumberOfComponents_eq_one G]

def FacialCycleOf (w : Cycle G) [Searchable G.dualGraph] : Prop :=
  ∃ (f : G.Faces), w.edges.toFinset = G.dualGraph.incEdges f


lemma three_le_dualGraph_minDegree [Fintype E] [G.Simple] : 3 ≤ G.dualGraph.minDegree := by
  by_contra! h
  unfold minDegree at h
  have := G.dualGraph.minDegreeVerts_nonempty
  sorry

lemma four_le_dualGraph_minDegree_of_bipartite [Fintype E] [G.Simple] [G.Bipartite] :
    4 ≤ G.dualGraph.minDegree := by
  sorry


end Graph
