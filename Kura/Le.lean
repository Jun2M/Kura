import Kura.Constructor

open Set Function

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph


/-- Subgraph order of Graph -/
instance instPartialOrderGraph : PartialOrder (Graph α β) where
  le G₁ G₂ := G₁.V ≤ G₂.V ∧ G₁.Inc₂ ≤ G₂.Inc₂
  le_refl G := by simp only [subset_refl, le_refl, implies_true, exists_const, and_self]
  le_trans G₁ G₂ G₃ h₁₂ h₂₃ := by
    obtain ⟨h₁₂v, h₁₂S⟩ := h₁₂
    obtain ⟨h₂₃v, h₂₃S⟩ := h₂₃
    exact ⟨h₁₂v.trans h₂₃v, h₁₂S.trans h₂₃S⟩
  le_antisymm G₁ G₂ h₁₂ h₂₁ := ext_inc₂ (h₁₂.1.antisymm h₂₁.1) fun e x y ↦ (by
    rw [h₁₂.2.antisymm h₂₁.2])

@[simp] lemma vx_subset_of_le (hle : G ≤ H) : G.V ⊆ H.V := hle.1

@[simp] lemma mem_of_le (hle : G ≤ H) : x ∈ G.V → x ∈ H.V := (hle.1 ·)

@[simp] lemma edge_subset_of_le (hle : G ≤ H) : G.E ⊆ H.E := edge_subset_of_inc₂_le_inc₂ hle.2

@[simp] lemma edge_mem_of_le (hle : G ≤ H) : e ∈ G.E → e ∈ H.E := (edge_subset_of_le hle ·)

lemma Inc_eq_Inc_of_le (hle : G ≤ H) (he : e ∈ G.E) : G.Inc e = H.Inc e := by
  rw [← inc₂_eq_inc₂_iff_inc_eq_inc]
  exact inc₂_eq_inc₂_of_edge_mem_and_inc₂_le_inc₂ he hle.2

lemma incFun_eq_incFun_of_le (hle : G ≤ H) (he : e ∈ G.E) : G.IncFun e = H.IncFun e := by
  rw [← inc_eq_inc_iff_incFun_eq_incFun]
  exact Inc_eq_Inc_of_le hle he

lemma Inc₂_eq_Inc₂_of_le (hle : G ≤ H) (he : e ∈ G.E) : G.Inc₂ e = H.Inc₂ e := by
  rw [inc₂_eq_inc₂_iff_inc_eq_inc]
  exact Inc_eq_Inc_of_le hle he

lemma le_of_exist_mutual_le (hle1 : G' ≤ H') (hle2 : H ≤ H') : G' ≤ H ↔ G'.V ⊆ H.V ∧ G'.E ⊆ H.E := by
  constructor
  · intro h
    exact ⟨vx_subset_of_le h, edge_subset_of_le h⟩
  · rintro ⟨hV, hE⟩
    refine ⟨hV, ?_⟩
    rintro e x y hbtw
    rwa [Inc₂_eq_Inc₂_of_le hle2 (hE hbtw.edge_mem), ← Inc₂_eq_Inc₂_of_le hle1 hbtw.edge_mem]

-- This is now the definition of `le`
lemma le_iff_inc₂ : G ≤ H ↔ G.V ⊆ H.V ∧ ∀ ⦃e u v⦄, G.Inc₂ e u v → H.Inc₂ e u v := Iff.rfl

@[simp]
lemma Inc₂.of_le (hle : G ≤ H) (h : G.Inc₂ e u v) : H.Inc₂ e u v := by
  rwa [← Inc₂_eq_Inc₂_of_le hle (edge_mem h)]

lemma Inc₂.le_of_le (hle : G ≤ H) : G.Inc₂ ≤ H.Inc₂ := hle.2

lemma inc₂_iff_inc₂_edge_mem_of_le (hle : G ≤ H) : G.Inc₂ e x y ↔ H.Inc₂ e x y ∧ e ∈ G.E := by
  rw [← and_iff_left_of_imp (Inc₂.edge_mem), and_congr_left_iff]
  rintro he
  rw [inc₂_eq_inc₂_of_edge_mem_and_inc₂_le_inc₂ he (Inc₂.le_of_le hle)]

@[simp]
lemma Inc.le (hle : G ≤ H) (hinc : G.Inc e x) : H.Inc e x := by
  rwa [← Inc_eq_Inc_of_le hle hinc.edge_mem]

lemma Inc.le_of_le (hle : G ≤ H) : G.Inc ≤ H.Inc := by
  rintro e x ⟨y, hbtw⟩
  use y, hbtw.of_le hle

lemma IsLoopAt_iff_IsLoopAt_of_edge_mem_le (hle : G ≤ H) (he : e ∈ G.E) :
    G.IsLoopAt e x ↔ H.IsLoopAt e x := by
  rw [← inc₂_eq_iff_isLoopAt, ← inc₂_eq_iff_isLoopAt]
  rw [Inc₂_eq_Inc₂_of_le hle he]

lemma IsLoopAt.le (hisLoopAt : G.IsLoopAt e x) (hle : G ≤ H) : H.IsLoopAt e x := by
  rwa [← IsLoopAt_iff_IsLoopAt_of_edge_mem_le hle hisLoopAt.edge_mem]

lemma IsNonloopAt_iff_IsNonloopAt_of_edge_mem_le (hle : G ≤ H) (he : e ∈ G.E) :
    G.IsNonloopAt e x ↔ H.IsNonloopAt e x := by
  rw [← inc_and_not_isLoopAt_iff_isNonloopAt, ← inc_and_not_isLoopAt_iff_isNonloopAt]
  refine Iff.and ?_ ?_
  · rw [Inc_eq_Inc_of_le hle he]
  · rw [IsLoopAt_iff_IsLoopAt_of_edge_mem_le hle he]

lemma IsNonloopAt.le (hisNonloopAt : G.IsNonloopAt e x) (hle : G ≤ H) : H.IsNonloopAt e x := by
  rwa [← IsNonloopAt_iff_IsNonloopAt_of_edge_mem_le hle hisNonloopAt.edge_mem]

lemma Adj.of_le (hle : G ≤ H) (hadj : G.Adj x y) : H.Adj x y := by
  obtain ⟨e, hbtw⟩ := hadj
  use e
  exact hbtw.of_le hle

lemma le_iff_inc : G ≤ H ↔ G.V ⊆ H.V ∧ G.E ⊆ H.E ∧ ∀ e ∈ G.E, ∀ v,
  G.Inc e v ↔ H.Inc e v := by
  constructor
  · rintro hle
    exact ⟨vx_subset_of_le hle, edge_subset_of_le hle, fun e he v ↦ by rw [Inc_eq_Inc_of_le hle he]⟩
  · refine fun ⟨hV, hE, hinc⟩ ↦ ⟨hV, fun e x y ↦ ?_⟩
    by_cases he : e ∈ G.E
    · rw [inc₂_eq_inc₂_iff_inc_eq_inc.mpr (by ext; exact hinc e he _)]
    · simp [he]

/-- If G₁ ≤ G₂ and G₂ is finite, then G₁ is finite too. -/
theorem finite_of_le_finite (hle : G ≤ H) [h : H.Finite] : G.Finite := by
  constructor
  · -- Prove the vertex set is finite
    apply Set.Finite.subset h.vx_fin
    exact vx_subset_of_le hle
  · -- Prove the edge set is finite
    apply Set.Finite.subset h.edge_fin
    exact edge_subset_of_le hle

lemma vx_ncard_le_of_le [hfin : H.Finite] (hle : G ≤ H) : G.V.ncard ≤ H.V.ncard :=
  Set.ncard_le_ncard (vx_subset_of_le hle) hfin.vx_fin

lemma edge_ncard_le_of_le [hfin : H.Finite] (hle : G ≤ H) : G.E.ncard ≤ H.E.ncard :=
  Set.ncard_le_ncard (edge_subset_of_le hle) hfin.edge_fin


instance instOrderBotGraph : OrderBot (Graph α β) where
  bot := Edgeless ∅ β
  bot_le G := by
    rw [le_iff_inc]
    refine ⟨?_, ?_⟩ <;> simp [Edgeless, empty_subset, mem_empty_iff_false,
    false_iff, IsEmpty.forall_iff, implies_true]

instance instInhabitedGraph : Inhabited (Graph α β) where
  default := ⊥

@[simp] lemma bot_V : (⊥ : Graph α β).V = ∅ := rfl

@[simp] lemma bot_E : (⊥ : Graph α β).E = ∅ := by
  simp only [edge_empty_iff_eq_Edgeless, bot_V]
  rfl

@[simp] lemma bot_incFun : (⊥ : Graph α β).IncFun = 0 := by simp

@[simp]
lemma bot_inc : (⊥ : Graph α β).Inc = fun _ _ ↦ False := by
  ext e a
  simp only [instOrderBotGraph, Edgeless.E, not_inc_of_E_empty]

@[simp]
lemma bot_inc₂ : (⊥ : Graph α β).Inc₂ = fun _ _ _ ↦ False := by
  ext e a b
  simp only [instOrderBotGraph, Edgeless.E, not_inc₂_of_E_empty]

@[simp]
lemma bot_adj : (⊥ : Graph α β).Adj = fun _ _ ↦ False := by
  ext x y
  simp only [instOrderBotGraph, Edgeless.E, not_adj_of_E_empty]

@[simp]
lemma vx_empty_iff_eq_bot : G.V = ∅ ↔ G = ⊥ := by
  constructor <;> rintro h
  · apply ext_inc h ?_
    simp only [instOrderBotGraph, Edgeless.E, not_inc_of_E_empty, iff_false]
    rintro e v hinc
    have := h ▸ hinc.vx_mem
    simp only [mem_empty_iff_false] at this
  · rw [h]
    rfl

lemma vx_disjoint_of_disjoint (hDisj : Disjoint G H) : Disjoint G.V H.V := by
  intro x hx1 hx2
  let X : Graph α β := Edgeless x β
  refine (hDisj (?_ : X ≤ G) ?_).1 <;>
  · rw [le_iff_inc]
    simpa [X]

-- Not True!
-- lemma Disjoint.edge_disjoint {G₁ G₂ : Graph α β} (hDisj : Disjoint G₁ G₂) : Disjoint G₁.E G₂.E := by


@[simp] lemma singleEdge_le_iff : Graph.singleEdge u v e ≤ G ↔ G.Inc₂ e u v := by
  simp only [le_iff_inc₂, singleEdge_V, Set.pair_subset_iff, singleEdge_inc₂_iff, and_imp, Sym2.eq_iff]
  refine ⟨fun h ↦ h.2 rfl (.inl ⟨rfl, rfl⟩), fun h ↦ ⟨⟨h.vx_mem_left, h.vx_mem_right⟩, ?_⟩⟩
  rintro e x y rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

section Union

/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α β) : Prop := ∀ ⦃e⦄, e ∈ G.E → e ∈ H.E → G.Inc₂ e = H.Inc₂ e

lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ hH hG ↦ (h hG hH).symm

/-- Two subgraphs of the same graph are compatible. -/
lemma compatible_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) :
    H₁.Compatible H₂ := by
  intro e he₁ he₂
  ext x y
  rw [inc₂_iff_inc₂_edge_mem_of_le h₁, inc₂_iff_inc₂_edge_mem_of_le h₂]
  simp [he₁, he₂]

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.

(If `G` and `H` are `Compatible`, this doesn't occur.)  -/
protected def union (G H : Graph α β) : Graph α β where
  V := G.V ∪ H.V
  E := G.E ∪ H.E
  Inc₂ e x y := G.Inc₂ e x y ∨ (e ∉ G.E ∧ H.Inc₂ e x y)
  symm e x y h := by beta_reduce at h ⊢; rwa [Inc₂.comm (G := G), Inc₂.comm (G := H)]
  vx_mem_left := by
    rintro e x y (h | h)
    · exact .inl h.vx_mem_left
    exact .inr h.2.vx_mem_left
  edge_mem _ _ _ h := h.elim (fun h' ↦ .inl h'.edge_mem) (fun h' ↦ .inr h'.2.edge_mem)
  exists_vx_inc₂ := by
    rw [← Set.union_diff_self]
    rintro e (he | ⟨heH, heG⟩)
    · obtain ⟨x, y, h⟩ := Inc₂.exists_vx_inc₂ he
      exact ⟨x, y, .inl h⟩
    obtain ⟨x, y, h⟩ := Inc₂.exists_vx_inc₂ heH
    exact ⟨x, y, .inr ⟨heG, h⟩⟩
  left_eq_of_inc₂ := by
    rintro e x y v w (h | h) (h' | h')
    · exact h.left_or_of_inc₂ h'
    · exact False.elim <| h'.1 h.edge_mem
    · exact False.elim <| h.1 h'.edge_mem
    exact h.2.left_or_of_inc₂ h'.2


instance : Union (Graph α β) where union := Graph.union

@[simp]
lemma union_vxSet (G H : Graph α β) : (G ∪ H).V = G.V ∪ H.V := rfl

@[simp]
lemma union_edgeSet (G H : Graph α β) : (G ∪ H).E = G.E ∪ H.E := rfl

lemma union_inc₂_iff : (G ∪ H).Inc₂ e x y ↔ G.Inc₂ e x y ∨ (e ∉ G.E ∧ H.Inc₂ e x y) := Iff.rfl

lemma union_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  suffices ∀ ⦃e : β⦄ ⦃x y : α⦄, H₁.Inc₂ e x y ∨ e ∉ H₁.E ∧ H₂.Inc₂ e x y → G.Inc₂ e x y by
    simpa [le_iff_inc₂, vx_subset_of_le h₁, vx_subset_of_le h₂, union_inc₂_iff]
  rintro e x y (h | ⟨-, h⟩) <;>
  exact h.of_le <| by assumption

@[simp]
lemma left_le_union (G H : Graph α β) : G ≤ G ∪ H := by
  simp_rw [le_iff_inc₂, union_inc₂_iff]
  tauto

lemma Compatible.union_inc₂_iff (h : Compatible G H) :
    (G ∪ H).Inc₂ e x y ↔ G.Inc₂ e x y ∨ H.Inc₂ e x y := by
  by_cases heG : e ∈ G.E
  · simp only [Graph.union_inc₂_iff, heG, not_true_eq_false, false_and, or_false, iff_self_or]
    exact fun heH ↦ by rwa [h heG heH.edge_mem]
  simp [Graph.union_inc₂_iff, heG]

lemma Compatible.union_comm (h : Compatible G H) : G ∪ H = H ∪ G :=
  Graph.ext_inc₂ (Set.union_comm ..) fun _ _ _ ↦ by rw [h.union_inc₂_iff, h.symm.union_inc₂_iff, or_comm]

lemma Compatible.right_le_union (h : Compatible G H) : H ≤ G ∪ H := by
  simp [h.union_comm]

lemma Compatible.union_le_iff {H₁ H₂ : Graph α β} (h_compat : H₁.Compatible H₂) :
    H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G :=
  ⟨fun h ↦ ⟨(left_le_union ..).trans h, (h_compat.right_le_union ..).trans h⟩,
    fun h ↦ union_le h.1 h.2⟩

@[simp]
lemma singleEdge_compatible_iff :
    (Graph.singleEdge x y e).Compatible G ↔ (e ∈ G.E → G.Inc₂ e x y) := by
  refine ⟨fun h he ↦ by simp [← h (by simp) he, singleEdge_inc₂_iff] , fun h f hf hfE ↦ ?_⟩
  obtain rfl : f = e := by simpa using hf
  ext u v
  rw [(h hfE).sym2_eq_iff, Graph.singleEdge_inc₂_iff, and_iff_right rfl]
  tauto

  -- simp +contextual [Graph.singleEdge_Inc₂, iff_def, or_imp]

end Union

section Intersection

protected def inter (G H : Graph α β) : Graph α β := ofInc₂ (G.V ∩ H.V)
  (fun e x y ↦ G.Inc₂ e x y ∧ H.Inc₂ e x y)
  (fun e x y h ↦ by beta_reduce at h ⊢; rwa [Inc₂.comm (G := G), Inc₂.comm (G := H)])
  (fun e x y h ↦ ⟨h.1.vx_mem_left, h.2.vx_mem_left⟩)
  (fun u v x y e huv hxy ↦ huv.1.left_or_of_inc₂ hxy.1)

instance : Inter (Graph α β) where inter := Graph.inter

@[simp]
lemma inter_vxSet (G H : Graph α β) : (G ∩ H).V = G.V ∩ H.V := rfl

@[simp]
lemma inter_edgeSet (G H : Graph α β) : (G ∩ H).E = {e | ∃ x y, G.Inc₂ e x y ∧ H.Inc₂ e x y} := rfl

lemma inter_inc₂_iff : (G ∩ H).Inc₂ e x y ↔ G.Inc₂ e x y ∧ H.Inc₂ e x y := Iff.rfl

lemma le_inter {H₁ H₂ : Graph α β} (h₁ : G ≤ H₁) (h₂ : G ≤ H₂) : G ≤ H₁ ∩ H₂ := by
  simp_rw [le_iff_inc₂, inter_inc₂_iff]
  simp +contextual only [inter_vxSet, subset_inter_iff, h₁, vx_subset_of_le, h₂, and_self,
    Inc₂.of_le h₁, Inc₂.of_le h₂, implies_true]

lemma inter_le_left {H₁ H₂ : Graph α β} : H₁ ∩ H₂ ≤ H₁ := by
  simp +contextual only [le_iff_inc₂, inter_vxSet, inter_subset_left, inter_inc₂_iff, implies_true,
    and_self]

lemma inter_le_right {H₁ H₂ : Graph α β} : H₁ ∩ H₂ ≤ H₂ := by
  simp +contextual only [le_iff_inc₂, inter_vxSet, inter_subset_right, inter_inc₂_iff, implies_true,
    and_self]

lemma le_inter_iff {H₁ H₂ : Graph α β} : G ≤ H₁ ∩ H₂ ↔ G ≤ H₁ ∧ G ≤ H₂ := by
  constructor
  · rintro h
    exact ⟨h.trans (inter_le_left), h.trans (inter_le_right)⟩
  · rintro ⟨h₁, h₂⟩
    exact le_inter h₁ h₂

end Intersection
