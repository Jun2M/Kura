import Kura.Basic


open Set Function
variable {α β : Type*} {G G₁ G₂ : Graph α β} {u v w x y : α} {e f g : β}
namespace Graph


/-- Subgraph order of Graph -/
instance instPartialOrderGraph : PartialOrder (Graph α β) where
  le G₁ G₂ := G₁.V ⊆ G₂.V ∧ G₁.E ⊆ G₂.E ∧ ∀ v e (hin : e ∈ G₁.E),
    G₁.Inc v e ↔ G₂.Inc v e
  le_refl G := by simp only [subset_refl, le_refl, implies_true, exists_const, and_self]
  le_trans G₁ G₂ G₃ h₁₂ h₂₃ := by
    obtain ⟨h₁₂v, h₁₂e, h₁₂S⟩ := h₁₂
    obtain ⟨h₂₃v, h₂₃e, h₂₃S⟩ := h₂₃
    refine ⟨h₁₂v.trans h₂₃v, h₁₂e.trans h₂₃e, ?_⟩
    rintro v e hin
    rw [h₁₂S _ _ hin, h₂₃S _ _ (h₁₂e hin)]
  le_antisymm G₁ G₂ h₁₂ h₂₁ := by
    ext1
    · exact h₁₂.1.antisymm h₂₁.1
    · exact h₁₂.2.1.antisymm h₂₁.2.1
    · rename_i v e
      by_cases h : e ∈ G₁.E
      · rw [h₁₂.2.2 _ _ h]
      · constructor <;> intro hInc <;> exfalso
        · exact h <| G₁.edge_mem_of_inc hInc
        · exact h <| (h₁₂.2.1.antisymm h₂₁.2.1) ▸ (G₂.edge_mem_of_inc hInc)

lemma vx_subset_of_le (hle : G₁ ≤ G₂) : G₁.V ⊆ G₂.V := hle.1

lemma edge_subset_of_le (hle : G₁ ≤ G₂) : G₁.E ⊆ G₂.E := hle.2.1

lemma Inc_iff_Inc_of_edge_mem_le (hle : G₁ ≤ G₂) (he : e ∈ G₁.E) : G₁.Inc v e ↔ G₂.Inc v e :=
  hle.2.2 _ _ he

lemma Inc.le (hinc : G₁.Inc x e) (hle : G₁ ≤ G₂) : G₂.Inc x e := by
  rwa [← hle.2.2 _ _ hinc.edge_mem]

lemma IsLoop_iff_IsLoop_of_edge_mem_le (hle : G₁ ≤ G₂) (he : e ∈ G₁.E) :
    G₁.IsLoop e ↔ G₂.IsLoop e := by
  constructor <;> rintro ⟨v, hinc, heq⟩
  · use v, (Inc_iff_Inc_of_edge_mem_le hle he).mp hinc
    intro y hy
    refine heq y ?_
    beta_reduce
    rwa [Inc_iff_Inc_of_edge_mem_le hle hinc.edge_mem]
  · use v, (Inc_iff_Inc_of_edge_mem_le hle he).mpr hinc
    intro y hy
    refine heq y ?_
    beta_reduce
    rwa [← Inc_iff_Inc_of_edge_mem_le hle he]

lemma IsLoop.le (hisLoop : G₁.IsLoop e) (hle : G₁ ≤ G₂) : G₂.IsLoop e := by
  rwa [← IsLoop_iff_IsLoop_of_edge_mem_le hle hisLoop.mem]

lemma Adj.le (hadj : G₁.Adj u v) (hle : G₁ ≤ G₂) : G₂.Adj u v := by
  obtain ⟨e, hinc, he⟩ := hadj
  use e, hinc.le hle
  split_ifs with hvw
  · subst v
    simp only [↓reduceIte] at he
    exact he.le hle
  · simp only [hvw, ↓reduceIte] at he
    exact he.le hle

lemma reflAdj.le (h : G₁.reflAdj u w) (hle : G₁ ≤ G₂) : G₂.reflAdj u w := by
  rw [reflAdj_iff_adj_or_eq] at h ⊢
  obtain hadj | ⟨rfl, hu⟩ := h
  · left
    exact hadj.le hle
  · right
    simp only [vx_subset_of_le hle hu, and_self]

lemma Connected.le (h : G₁.Connected u v) (hle : G₁ ≤ G₂) : G₂.Connected u v := by
  induction h with
  | single huv => exact Relation.TransGen.single (huv.le hle)
  | tail huv h ih => exact Relation.TransGen.tail ih (h.le hle)

@[simp]
instance instOrderBotGraph : OrderBot (Graph α β) where
  bot := {
    V := ∅,
    E := ∅,
    Inc v e := False,
    vx_mem_of_inc := by simp only [mem_empty_iff_false, imp_self, implies_true],
    edge_mem_of_inc := by simp only [mem_empty_iff_false, imp_self, implies_true],
    exists_vertex_inc := by simp only [mem_empty_iff_false, exists_false, imp_self, implies_true],
    not_hypergraph := by simp only [IsEmpty.forall_iff, implies_true]
  }
  bot_le G := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [empty_subset]
    · simp only [empty_subset]
    · simp only [mem_empty_iff_false, false_iff, IsEmpty.forall_iff, implies_true]

instance instInhabitedGraph : Inhabited (Graph α β) where
  default := ⊥


/-- Induced subgraph -/
def induce (G : Graph α β) (U : Set α) : Graph α β where
  V := G.V ∩ U
  E := G.E ∩ {e | ∀ (x : α), G.Inc x e → x ∈ U}
  Inc v e := G.Inc v e ∧ ∀ (x : α), G.Inc x e → x ∈ U
  vx_mem_of_inc x y h := by
    obtain ⟨hinc, hU⟩ := h
    exact ⟨G.vx_mem_of_inc hinc, hU _ hinc⟩
  edge_mem_of_inc v e h := by
    simp only [mem_inter_iff, mem_setOf_eq]
    obtain ⟨hinc, hU⟩ := h
    exact ⟨hinc.edge_mem, hU⟩
  exists_vertex_inc e he := by
    obtain ⟨v, hv⟩ := G.exists_vertex_inc he.1
    obtain ⟨he, hU⟩ := he
    use v, hv, hU
  not_hypergraph x y z e := by
    rintro ⟨hx, _⟩ ⟨hy, _⟩ ⟨hz, hU⟩
    obtain h | h | h := G.not_hypergraph hx hy hz <;>
    simp only [h, true_or, or_true]

notation G "[" S "]" => Graph.induce G S

@[simp]
abbrev vxDel (G : Graph α β) (V : Set α) : Graph α β := G[G.V \ V]

@[simp]
lemma induce_V : (G[U]).V = G.V ∩ U := rfl

@[simp]
lemma induce_E : (G[U]).E = G.E ∩ {e | ∀ (x : α), G.Inc x e → x ∈ U} := rfl

@[simp]
lemma induce_inc : (G[U]).Inc v e ↔ G.Inc v e ∧ ∀ (x : α), G.Inc x e → x ∈ U := by
  simp only [induce]

@[simp]
theorem induce_le_induce_iff {U V : Set α} : G[U] ≤ G[V] ↔ G.V ∩ U ⊆ G.V ∩ V := by
  refine ⟨vx_subset_of_le, ?_⟩
  rintro h
  refine ⟨h, ?_, ?_⟩
  · intro e
    simp only [induce_E, mem_inter_iff, mem_setOf_eq, and_imp]
    intro he hU
    use he
    intro x hinc
    exact (h ⟨hinc.vx_mem, hU x hinc⟩).2
  · simp only [induce_E, mem_inter_iff, mem_setOf_eq, induce_inc, and_congr_right_iff, and_imp]
    rintro v e he hU hinc
    rw [iff_true_left hU]
    intro x hinc
    exact (h ⟨hinc.vx_mem, hU x hinc⟩).2

@[simp]
theorem induce_eq_induce_iff {U V : Set α} : G[U] = G[V] ↔ G.V ∩ U = G.V ∩ V := by
  rw [le_antisymm_iff, subset_antisymm_iff, induce_le_induce_iff, induce_le_induce_iff]

@[simp]
theorem induce_eq_self_iff {U : Set α} : G[U] = G ↔ G.V ⊆ U := by
  constructor <;> intro h
  · rw [← h]
    simp only [induce_V, inter_subset_right]
  · ext1
    · simp only [induce, inter_eq_left, h]
    · simp only [induce, inter_eq_left]
      rintro e he v hinc
      exact h hinc.vx_mem
    · simp only [induce, and_iff_left_iff_imp]
      rintro hinc x hx
      exact h hx.vx_mem

@[simp]
lemma induce_univ_eq_self : G[Set.univ] = G := induce_eq_self_iff.mpr (fun ⦃_a⦄ _a ↦ trivial)

@[simp]
lemma induce_V_eq_self  : G[G.V] = G := induce_eq_self_iff.mpr subset_rfl

@[simp]
lemma induce_empty_eq_bot : G[∅] = ⊥ := by
  ext1
  · simp only [induce, inter_empty, mem_empty_iff_false, imp_false, instOrderBotGraph]
  · ext e
    simp only [induce, inter_empty, mem_empty_iff_false, imp_false, mem_inter_iff, mem_setOf_eq,
      instOrderBotGraph, iff_false, not_and, not_forall, not_not]
    exact (G.exists_vertex_inc ·)
  · simp only [induce, inter_empty, mem_empty_iff_false, imp_false, instOrderBotGraph, iff_false,
    not_and, not_forall, not_not]
    rintro hinc
    exact G.exists_vertex_inc hinc.edge_mem

@[simp]
lemma induce_le (G : Graph α β) (U : Set α) : G[U] ≤ G := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [induce, inter_subset_left, mem_inter_iff, mem_setOf_eq,
    and_iff_left_iff_imp, and_imp]
  rintro v e he hU hinc
  exact hU

@[simp]
lemma induce_mono (G : Graph α β) (U V : Set α) (hsu : U ⊆ V) : G[U] ≤ G[V] := by
  rw [induce_le_induce_iff]
  rintro x ⟨hx, hU⟩
  exact ⟨hx, hsu hU⟩

@[simp]
lemma induce_induce_eq_induce_inter (U V : Set α) : G[U][V] = G[U ∩ V] := by
  ext1
  · simp only [induce, and_imp, mem_inter_iff]
    exact inter_assoc G.V U V
  · ext e
    simp only [induce, and_imp, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨he, hmemU⟩, hmemV⟩
      refine ⟨he, fun x hinc ↦ ⟨hmemU x hinc, hmemV x hinc hmemU⟩⟩
    · rintro ⟨he, hUV⟩
      simp only [he, true_and]
      refine ⟨fun x a ↦ mem_of_mem_inter_left (hUV x a), ?_⟩
      rintro x hx' h
      exact mem_of_mem_inter_right (hUV x hx')
  · rename_i v e
    simp only [induce, and_imp, mem_inter_iff]
    constructor
    · rintro ⟨⟨hinc, hU⟩, hV⟩
      simp only [hinc, true_and]
      rintro x hinc
      exact ⟨hU x hinc, hV x hinc hU⟩
    · rintro ⟨hinc, hUV⟩
      refine ⟨⟨hinc, fun x a ↦ (hUV x a).1⟩, ?_⟩
      rintro x hinc hU
      exact mem_of_mem_inter_right (hUV x hinc)

@[simp]
lemma induce_idem (U : Set α) : G[U][U] = G[U] := by
  convert G.induce_induce_eq_induce_inter U U
  simp only [inter_self]



/-- Restrict a graph to a set of edges -/
def restrict (G : Graph α β) (R : Set β) : Graph α β where
  V := G.V
  E := G.E ∩ R
  Inc v e := G.Inc v e ∧ e ∈ R
  vx_mem_of_inc _ _ h := G.vx_mem_of_inc h.1
  edge_mem_of_inc _ _ h := ⟨h.1.edge_mem, h.2⟩
  exists_vertex_inc e he := by
    obtain ⟨v, hv⟩ := G.exists_vertex_inc he.1
    exact ⟨v, hv, he.2⟩
  not_hypergraph _ _ _ _ hex hey hez := G.not_hypergraph hex.1 hey.1 hez.1

notation G "{" S "}" => Graph.restrict G S

@[simp]
abbrev edgeDel (G : Graph α β) (F : Set β) : Graph α β := G{G.E \ F}

@[simp]
lemma restrict_V : (G{R}).V = G.V := rfl

@[simp]
lemma restrict_E : (G{R}).E = G.E ∩ R := rfl

@[simp]
lemma restrict_inc : (G{R}).Inc v e ↔ G.Inc v e ∧ e ∈ R := by
  simp only [restrict]

lemma reflAdj.restrict_of_le_reflAdj_restrict (hle : G₁ ≤ G₂) {S : Set β}
    (hSconn : G₂{S}.reflAdj u v) (h : G₂.E ∩ S ⊆ G₁.E) (hu : u ∈ G₁.V) : G₁{S}.reflAdj u v := by
  unfold reflAdj at hSconn
  split_ifs at hSconn with heq
  · subst heq
    exact reflAdj.rfl hu
  · obtain ⟨e, ⟨huinc, heS⟩, ⟨hvinc, _⟩⟩ := hSconn
    refine Inc.reflAdj_of_inc (e := e) ⟨?_, heS⟩ ⟨?_, heS⟩ <;>
    rwa [Inc_iff_Inc_of_edge_mem_le hle (h ⟨huinc.edge_mem, heS⟩)]

lemma Connected.restrict_of_le_connected_restrict (hle : G₁ ≤ G₂) {S : Set β}
    (hSconn : G₂{S}.Connected u v) (h : G₂.E ∩ S ⊆ G₁.E) (hu : u ∈ G₁.V) : G₁{S}.Connected u v := by
  induction hSconn with
  | single hradj =>
    rename_i v
    apply reflAdj.connected
    apply hradj.restrict_of_le_reflAdj_restrict hle h hu
  | tail _hconn hradj ih =>
    apply ih.trans
    rename_i x y
    apply reflAdj.connected
    apply hradj.restrict_of_le_reflAdj_restrict hle h
    exact ih.symm.mem

@[simp]
theorem restrict_le_restrict_iff (G : Graph α β) (R S : Set β) :
    G{R} ≤ G{S} ↔ G.E ∩ R ⊆ G.E ∩ S := by
  refine ⟨edge_subset_of_le, ?_⟩
  rintro h
  refine ⟨subset_rfl, h, ?_⟩
  simp only [restrict_inc, and_congr_right_iff]
  rintro v e he hinc
  simp [he.2, (h he).2]

@[simp]
theorem restrict_eq_restrict_iff (G : Graph α β) (R S : Set β) :
    G{R} = G{S} ↔ G.E ∩ R = G.E ∩ S := by
  rw [le_antisymm_iff, subset_antisymm_iff, restrict_le_restrict_iff, restrict_le_restrict_iff]

@[simp]
theorem restrict_eq_self_iff (G : Graph α β) (R : Set β) : G{R} = G ↔ G.E ⊆ R := by
  constructor <;> intro h
  · rw [← h]
    simp only [restrict_E, inter_subset_right]
  · ext1
    · simp only [restrict]
    · simp only [restrict_E, inter_eq_left, h]
    · simp only [restrict_inc, and_iff_left_iff_imp]
      intro hinc
      exact h hinc.edge_mem

@[simp]
lemma restrict_univ_eq_self : G{Set.univ} = G := by
  rw [restrict_eq_self_iff]
  exact subset_univ _

@[simp]
lemma restrict_E_eq_self : G{G.E} = G := by
  rw [restrict_eq_self_iff]

@[simp]
lemma restrict_le (G : Graph α β) (R : Set β) : G{R} ≤ G := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [restrict, subset_refl, inter_subset_left, mem_inter_iff,
    and_iff_left_iff_imp, and_imp]
  rintro v e he hmemR hinc
  exact hmemR

@[simp]
lemma restrict_mono (G : Graph α β) (R S : Set β) (h : R ⊆ S) : G{R} ≤ G{S} := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [restrict, subset_refl, inter_subset_left, mem_inter_iff,
    and_iff_left_iff_imp, and_imp]
  · exact inter_subset_inter (fun ⦃a⦄ a ↦ a) h
  · rintro v e he hmemR
    simp only [hmemR, and_true, h hmemR]

@[simp]
theorem restrict_restrict_eq_restrict_inter (R S : Set β) : G{R}{S} = G{R ∩ S} := by
  ext1
  · simp only [restrict, inter_assoc, mem_inter_iff]
  · simp only [restrict, mem_inter_iff]
    rw [← inter_assoc]
  · rename_i v e
    simp only [restrict, mem_inter_iff]
    rw [and_assoc]

@[simp]
lemma restrict_idem (R : Set β) : G{R}{R} = G{R} := by
  convert G.restrict_restrict_eq_restrict_inter R R
  simp only [inter_self]

/-- G{R}[U] is the prefered notation for explicit subgraph over G[U]{R} -/
lemma induce_restrict_eq_restrict_induce (U : Set α) (R : Set β) :
    G[U]{R} = G{R}[U] := by
  ext1
  · simp only [restrict, induce, and_imp]
  · simp only [restrict, induce, and_imp]
    ext e
    constructor
    · rintro ⟨⟨he, hmemU⟩, hmemR⟩
      simp_all only [mem_inter_iff, mem_setOf_eq, imp_self, implies_true, and_self]
      -- refine ⟨⟨he, fun x a a_1 ↦ hmemU x a⟩, hmemR, fun x a a_1 ↦ hmemU x a⟩
    · rintro ⟨⟨he, hR⟩, hU⟩
      simp_all only [imp_self, implies_true, forall_const, mem_inter_iff, mem_setOf_eq, and_self]
      -- refine ⟨⟨he, fun x a ↦ hmemU x a hmemR⟩, hmemR⟩
  · rename_i v e
    simp only [restrict, induce, mem_toSym2_iff_inc, exists_prop, and_imp, mem_inter_iff, sep_inter]
    constructor
    · rintro ⟨⟨hinc, hU⟩, hR⟩
      simp_all only [and_self, imp_self, implies_true]
      -- refine ⟨⟨hinc, hmemR⟩, ⟨⟨he, hmemR⟩, fun x a a_1 ↦ hmemU x a⟩⟩
    · rintro ⟨⟨hinc, hR⟩, hU⟩
      simp_all only [forall_const, implies_true, and_self]
      -- refine ⟨⟨hinc, he, fun x a ↦ hmemU x a hmemR⟩, hmemR⟩

/-- From here `subgraph` refers to G{R}[U] -/
@[simp]
theorem induce_restrict_eq_subgraph (U : Set α) (R : Set β) :
    G[U]{R} = G{R}[U] := G.induce_restrict_eq_restrict_induce U R

lemma subgraph_le (G : Graph α β) (U : Set α) (R : Set β) : G{R}[U] ≤ G :=
  (Graph.induce_le _ U).trans (G.restrict_le R)

/-- Implicit subgraph iff explicit subgraph-/
theorem exists_subgraph_of_le : G₁ ≤ G₂ ↔ G₁ = G₂{G₁.E}[G₁.V] := by
  constructor
  · rintro hle
    ext1
    · simp only [induce_V, restrict_V, right_eq_inter, vx_subset_of_le hle]
    · ext e
      simp only [induce_E, restrict_E, restrict_inc, and_imp, mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro he1
        use ⟨edge_subset_of_le hle he1, he1⟩
        rintro x hinc _
        rw [← Inc_iff_Inc_of_edge_mem_le hle he1] at hinc
        exact hinc.vx_mem
      · rintro ⟨⟨he2, he1⟩, hx1⟩
        exact he1
    · simp only [induce_inc, restrict_inc, and_imp]
      constructor
      · rintro hinc1
        use ⟨hinc1.le hle, hinc1.edge_mem⟩
        rintro x hinc2 hmem1
        rw [← Inc_iff_Inc_of_edge_mem_le hle hmem1] at hinc2
        exact hinc2.vx_mem
      · rintro ⟨⟨hinc2, hmem1⟩, hx1⟩
        rwa [← Inc_iff_Inc_of_edge_mem_le hle hmem1] at hinc2
  · rintro heq
    rw [heq]
    exact G₂.subgraph_le G₁.V G₁.E
