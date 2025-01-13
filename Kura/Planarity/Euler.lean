import Kura.Planarity.Plainarity

namespace Graph
variable {V E F : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq F] (G : Graph V E)
  [Undirected G] [Planar_by_AbstractDual G]

lemma Faces_card_eq_one_of_no_edges [IsEmpty E] :
    @Fintype.card G.Faces (by have := Fintype.ofIsEmpty (α := E); infer_instance) = 1 := by
  sorry

lemma EulerFormula_aux [Nonempty V] [Fintype V] [Fintype E]:
    Fintype.card E = m →
      Fintype.card V + Fintype.card G.Faces - Fintype.card E = 1 + NumberOfComponents G := by
  have hVpos : Fintype.card V > 0 := Fintype.card_pos
  induction m generalizing E with
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
    let hSubgraph : G'.SubgraphOf G := (Es_spanningsubgraph G {e}ᶜ).toSubgraphOf
    have hG'Undir : G'.Undirected := hSubgraph.Undirected
    have hG'Planar : Planar_by_AbstractDual G' := by sorry
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

    let u := G.v1 e
    let v := G.v2 e
    by_cases hG'conn : G'.conn u v
    · have hNC : G'.NumberOfComponents = G.NumberOfComponents := by
        unfold Graph.NumberOfComponents
        have hconnEq : G'.connSetoid = G.connSetoid := by
          ext x y
          refine Es_subgraph_conn_eq_conn_iff ?_ x y
          rintro e' h
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Decidable.not_not] at h
          subst e'
          exact hG'conn

        apply_fun Quotient at hconnEq
        have : Fintype (Quotient G'.connSetoid) :=
          @Quotient.fintype _ _  G'.connSetoid (fun u v ↦ Relation.ReflTransGenDeciable _ _)
        have : Fintype (Quotient G.connSetoid) :=
          @Quotient.fintype _ _ G.connSetoid (fun u v ↦ Relation.ReflTransGenDeciable _ _)
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
  ∃ (f : G.Faces), w.edges.toFinset = (G.dualGraph.incEdges f).toFinset

instance instSearchableDualGraph [Fintype E] [G.Simple] :
    Searchable G.dualGraph := by
  sorry

lemma three_le_dualGraph_minDegree [Fintype E] [G.Simple]:
    3 ≤ G.dualGraph.minDegree := by
  by_contra! h
  unfold minDegree at h
  have := G.dualGraph.minDegreeVerts_nonempty
  sorry

lemma four_le_dualGraph_minDegree_of_bipartite [Fintype E] [G.Simple] [G.Bipartite] :
    4 ≤ G.dualGraph.minDegree := by
  sorry

end Graph
