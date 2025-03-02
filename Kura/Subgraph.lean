import Kura.Basic


open Set Function
variable {α β : Type*} {G G₁ G₂ : Graph α β} {u v w x y : α} {e f g : β}
namespace Graph


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

lemma V_subset_of_le (hle : G₁ ≤ G₂) : G₁.V ⊆ G₂.V := hle.1

lemma E_subset_of_le (hle : G₁ ≤ G₂) : G₁.E ⊆ G₂.E := hle.2.1

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

private lemma preconn_le (h : G₁.Adj u w ∨ u = w ∧ u ∈ G₁.V) (hle : G₁ ≤ G₂) :
    G₂.Adj u w ∨ u = w ∧ u ∈ G₂.V := by
  obtain hadj | ⟨rfl, hu⟩ := h
  · left
    exact hadj.le hle
  · right
    refine ⟨rfl, V_subset_of_le hle hu⟩

lemma Connected.le (h : G₁.Connected u v) (hle : G₁ ≤ G₂) : G₂.Connected u v := by
  induction h with
  | single huv => exact Relation.TransGen.single (preconn_le huv hle)
  | tail huv h ih => exact Relation.TransGen.tail ih (preconn_le h hle)

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


def induce (G : Graph α β) (U : Set α) : Graph α β where
  V := G.V ∩ U
  E := {e | ∃ (he : e ∈ G.E), ∀ x ∈ G.toSym2 he, x ∈ U}
  Inc v e := G.Inc v e ∧ ∃ (he : e ∈ G.E), ∀ x ∈ G.toSym2 he, x ∈ U
  vx_mem_of_inc x y h := by
    obtain ⟨hinc, he, hx⟩ := h
    refine ⟨G.vx_mem_of_inc hinc, hx _ ?_⟩
    exact mem_toSym2_of_inc hinc
  edge_mem_of_inc v e h := by
    simp only [mem_inter_iff, mem_setOf_eq, and_exists_self]
    obtain ⟨he, hmem, hx⟩ := h
    exact ⟨hmem, hx⟩
  exists_vertex_inc e he := by
    obtain ⟨v, hv⟩ := G.exists_vertex_inc he.1
    obtain ⟨he, h⟩ := he
    use v, hv, he
  not_hypergraph x y z e := by
    rintro ⟨hx, he, hx'⟩ ⟨hy, he', hy'⟩ ⟨hz, he'', hz'⟩
    obtain h | h | h := G.not_hypergraph hx hy hz <;>
    simp only [h, true_or, or_true]

notation G "[" S "]" => Graph.induce G S

def vxDel (G : Graph α β) (V : Set α) : Graph α β := G[G.V \ V]

lemma induce_eq_self {U : Set α} (h : G.V ⊆ U) : G[U] = G := by
  ext1
  · simp only [induce, mem_toSym2_iff_inc, exists_prop, inter_eq_left, h]
  · simp only [induce, mem_toSym2_iff_inc, exists_prop, sep_eq_self_iff_mem_true]
    rintro e he v hinc
    exact h hinc.vx_mem
  · simp only [induce, mem_toSym2_iff_inc, exists_prop, and_iff_left_iff_imp]
    rename_i v e
    rintro hinc
    use hinc.edge_mem
    rintro x hx
    exact h hx.vx_mem

@[simp]
lemma induce_univ_eq_self : G[Set.univ] = G := induce_eq_self (fun ⦃_a⦄ _a ↦ trivial)

@[simp]
lemma induce_empty_eq_bot : G[∅] = ⊥ := by
  ext1
  · simp only [induce, inter_empty, mem_toSym2_iff_inc, mem_empty_iff_false, imp_false,
    exists_prop, instOrderBotGraph]
  · simp only [induce, inter_empty, mem_toSym2_iff_inc, mem_empty_iff_false, imp_false,
    exists_prop, instOrderBotGraph, sep_eq_empty_iff_mem_false, not_forall, not_not]
    rintro e he
    exact G.exists_vertex_inc he
  · simp only [induce, inter_empty, mem_toSym2_iff_inc, mem_empty_iff_false, imp_false,
    exists_prop, instOrderBotGraph, iff_false, not_and, not_forall, not_not]
    rintro hinc he
    exact G.exists_vertex_inc he

@[simp]
lemma induce_le (U : Set α) : G[U] ≤ G := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [induce, subset_inter_iff, inter_subset_left, true_and,
    Pi.le_def, le_Prop_eq, and_imp, mem_toSym2_iff_inc, forall_exists_index, exists_prop, sep_subset,
    mem_setOf_eq, and_iff_left_iff_imp, and_imp]
  rintro v e he h hinc
  exact ⟨he, h⟩

@[simp]
lemma induce_mono (U V : Set α) (hsu : U ⊆ V) : G[U] ≤ G[V] := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [induce, subset_inter_iff, inter_subset_left, true_and]
    exact Subset.trans inter_subset_right hsu
  · simp only [induce, mem_toSym2_iff_inc, exists_prop, setOf_subset_setOf, and_imp]
    rintro e he hmemU
    use he, fun x a ↦ hsu (hmemU x a)
  · simp only [induce, mem_toSym2_iff_inc, exists_prop, mem_setOf_eq, and_congr_right_iff, and_imp]
    rintro v e he hmemU hInc _
    constructor
    · rintro h x hinc
      exact hsu <| h x hinc
    · rintro h x hinc
      exact hmemU x hinc

@[simp]
lemma induce_induce_eq_induce_inter (G : Graph α β) (U V : Set α) : G[U][V] = G[U ∩ V] := by
  ext1
  · simp only [induce, mem_toSym2_iff_inc, exists_prop, and_imp, mem_setOf_eq, mem_inter_iff]
    exact inter_assoc G.V U V
  · simp only [induce, mem_toSym2_iff_inc, exists_prop, and_imp, mem_setOf_eq, mem_inter_iff]
    ext e
    constructor
    · rintro ⟨⟨he, hmemU⟩, hmemV⟩
      refine ⟨he, fun x hinc ↦ ⟨hmemU x hinc, hmemV x hinc he hmemU⟩⟩
    · rintro ⟨he, hx⟩
      simp only [mem_setOf_eq, he, true_and, forall_const]
      refine ⟨fun x a ↦ mem_of_mem_inter_left (hx x a), ?_⟩
      rintro x hx' h
      exact mem_of_mem_inter_right (hx x hx')
  · rename_i v e
    simp only [induce, mem_toSym2_iff_inc, exists_prop, and_imp, mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨⟨hinc, he, hU⟩, ⟨_, b⟩⟩
      simp only [hinc, he, true_and]
      rintro x hx
      exact ⟨hU x hx, b x hx he hU⟩
    · rintro ⟨hinc, ⟨he, hUV⟩⟩
      refine ⟨⟨hinc, he, fun x a ↦ (hUV x a).1⟩, ⟨⟨he, fun x a ↦ (hUV x a).1⟩, ?_⟩⟩
      rintro x hinc he hU
      exact mem_of_mem_inter_right (hUV x hinc)

@[simp]
lemma induce_idem (G : Graph α β) (U : Set α) : G[U][U] = G[U] := by
  convert G.induce_induce_eq_induce_inter U U
  simp only [inter_self]




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

def edgeDel (G : Graph α β) (F : Set β) : Graph α β := G{G.E \ F}

lemma restrict_eq_self (G : Graph α β) (F : Set β) (h : G.E ⊆ F) : G{F} = G := by
  ext1
  · simp only [restrict]
  · simp only [restrict, inter_eq_left, h]
  · rename_i v e
    simp only [restrict, and_iff_left_iff_imp]
    exact fun a ↦ h (Inc.edge_mem a)

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
lemma restrict_restrict_eq_restrict_inter (G : Graph α β) (R S : Set β) : G{R}{S} = G{R ∩ S} := by
  ext1
  · simp only [restrict, inter_assoc, mem_inter_iff]
  · simp only [restrict, mem_inter_iff]
    rw [← inter_assoc]
  · rename_i v e
    simp only [restrict, mem_inter_iff]
    rw [and_assoc]

@[simp]
lemma restrict_idem (G : Graph α β) (R : Set β) : G{R}{R} = G{R} := by
  convert G.restrict_restrict_eq_restrict_inter R R
  simp only [inter_self]

@[simp]
lemma induce_restrict_eq_restrict_induce (G : Graph α β) (U : Set α) (R : Set β) :
    G[U]{R} = G{R}[U] := by
  ext1
  · simp only [restrict, induce, mem_toSym2_iff_inc, exists_prop, and_imp, mem_inter_iff,
    sep_inter]
  · simp only [restrict, induce, mem_toSym2_iff_inc, exists_prop, and_imp, mem_inter_iff,
    sep_inter]
    ext e
    constructor
    · rintro ⟨⟨he, hmemU⟩, hmemR⟩
      simp_all only [mem_inter_iff, mem_setOf_eq, imp_self, implies_true, and_self]
      -- refine ⟨⟨he, fun x a a_1 ↦ hmemU x a⟩, hmemR, fun x a a_1 ↦ hmemU x a⟩
    · rintro ⟨⟨he, hmemU⟩, hmemR, _⟩
      simp_all only [imp_self, implies_true, forall_const, mem_inter_iff, mem_setOf_eq, and_self]
      -- refine ⟨⟨he, fun x a ↦ hmemU x a hmemR⟩, hmemR⟩
  · rename_i v e
    simp only [restrict, induce, mem_toSym2_iff_inc, exists_prop, and_imp, mem_inter_iff, sep_inter]
    constructor
    · rintro ⟨⟨hinc, he, hmemU⟩, hmemR⟩
      simp_all only [and_self, imp_self, implies_true]
      -- refine ⟨⟨hinc, hmemR⟩, ⟨⟨he, hmemR⟩, fun x a a_1 ↦ hmemU x a⟩⟩
    · rintro ⟨⟨hinc, _⟩, ⟨⟨he, hmemR⟩, hmemU⟩⟩
      simp_all only [forall_const, implies_true, and_self]
      -- refine ⟨⟨hinc, he, fun x a ↦ hmemU x a hmemR⟩, hmemR⟩
