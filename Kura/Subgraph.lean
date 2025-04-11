import Kura.Isolated


open Set Function
variable {α β : Type*} {G G₁ G₂ : Graph α β} {u v w x y : α} {e f g : β}
namespace Graph


/-- Subgraph order of Graph -/
instance instPartialOrderGraph : PartialOrder (Graph α β) where
  le G₁ G₂ := G₁.V ⊆ G₂.V ∧ G₁.E ⊆ G₂.E ∧ ∀ e (hin : e ∈ G₁.E), G₁.incFun e = G₂.incFun e
  le_refl G := by simp only [subset_refl, le_refl, implies_true, exists_const, and_self]
  le_trans G₁ G₂ G₃ h₁₂ h₂₃ := by
    obtain ⟨h₁₂v, h₁₂e, h₁₂S⟩ := h₁₂
    obtain ⟨h₂₃v, h₂₃e, h₂₃S⟩ := h₂₃
    refine ⟨h₁₂v.trans h₂₃v, h₁₂e.trans h₂₃e, ?_⟩
    rintro e he
    rw [h₁₂S _ he, h₂₃S _ (h₁₂e he)]
  le_antisymm G₁ G₂ h₁₂ h₂₁ := by
    ext1
    · exact h₁₂.1.antisymm h₂₁.1
    · exact h₁₂.2.1.antisymm h₂₁.2.1
    · ext e x
      by_cases h : e ∈ G₁.E
      · rw [h₁₂.2.2 _ h]
      · have : e ∉ G₂.E := by
          contrapose! h
          exact h₂₁.2.1 h
        simp only [h, not_false_eq_true, incFun_of_not_mem_edgeSet, Finsupp.coe_zero, Pi.zero_apply,
          this]

@[simp]
lemma vx_subset_of_le (hle : G₁ ≤ G₂) : G₁.V ⊆ G₂.V := hle.1

@[simp]
lemma mem_of_le (hle : G₁ ≤ G₂) : x ∈ G₁.V → x ∈ G₂.V := (hle.1 ·)

@[simp]
lemma edge_subset_of_le (hle : G₁ ≤ G₂) : G₁.E ⊆ G₂.E := hle.2.1

@[simp]
lemma edge_mem_of_le (hle : G₁ ≤ G₂) : e ∈ G₁.E → e ∈ G₂.E := (hle.2.1 ·)

lemma Inc_iff_Inc_of_le {e : β} (hle : G₁ ≤ G₂) (he : e ∈ G₁.E) : G₁.Inc e v ↔ G₂.Inc e v := by
  unfold Inc
  rw [hle.2.2 e he]

lemma incFun_eq_incFun_of_le (hle : G₁ ≤ G₂) (he : e ∈ G₁.E) : G₁.incFun e = G₂.incFun e :=
  hle.2.2 e he

@[simp]
lemma Inc.le (hinc : G₁.Inc e x) (hle : G₁ ≤ G₂) : G₂.Inc e x := by
  rwa [← Inc_iff_Inc_of_le hle hinc.edge_mem]

lemma IsLoop_iff_IsLoop_of_edge_mem_le (hle : G₁ ≤ G₂) (he : e ∈ G₁.E) :
    G₁.IsLoopAt e x ↔ G₂.IsLoopAt e x := by
  unfold IsLoopAt
  rw [incFun_eq_incFun_of_le hle he]

lemma IsLoop.le (hisLoopAt : G₁.IsLoopAt e x) (hle : G₁ ≤ G₂) : G₂.IsLoopAt e x := by
  rwa [← IsLoop_iff_IsLoop_of_edge_mem_le hle hisLoopAt.edge_mem]

lemma le_iff_inc : G₁ ≤ G₂ ↔ G₁.V ⊆ G₂.V ∧ G₁.E ⊆ G₂.E ∧ ∀ e ∈ G₁.E, ∀ v,
  G₁.Inc e v ↔ G₂.Inc e v := by
  constructor
  · rintro ⟨hV, hE, hinc⟩
    refine ⟨hV, hE, fun e he v ↦ ?_⟩
    unfold Inc
    rw [hinc e he]
  · refine fun ⟨hV, hE, hinc⟩ ↦ ⟨hV, hE, fun e he ↦ ?_⟩
    rw [← inc_eq_inc_iff]
    ext x
    exact hinc e he x

lemma le_iff_inc₂ : G₁ ≤ G₂ ↔ G₁.V ⊆ G₂.V ∧ G₁.E ⊆ G₂.E ∧ ∀ e ∈ G₁.E, ∀ v w,
  G₁.Inc₂ e v w ↔ G₂.Inc₂ e v w := by
  constructor
  · rintro ⟨hV, hE, hinc⟩
    refine ⟨hV, hE, fun e he v w ↦ ?_⟩
    unfold Inc₂ toMultiset
    rw [hinc e he]
  · refine fun ⟨hV, hE, hinc⟩ ↦ ⟨hV, hE, fun e he ↦ ?_⟩
    rw [← inc₂_eq_inc₂_iff]
    ext v w
    exact hinc e he v w

lemma inc₂_iff_inc₂_of_edge_mem_le (hle : G₁ ≤ G₂) (he : e ∈ G₁.E) :
    G₁.Inc₂ e u v ↔ G₂.Inc₂ e u v := by
  unfold Inc₂ toMultiset
  rw [incFun_eq_incFun_of_le hle he]

lemma Inc₂.le (h : G₁.Inc₂ e u v) (hle : G₁ ≤ G₂) : G₂.Inc₂ e u v := by
  rwa [← inc₂_iff_inc₂_of_edge_mem_le hle (edge_mem h)]

lemma Adj.le (hadj : G₁.Adj u v) (hle : G₁ ≤ G₂) : G₂.Adj u v := by
  obtain ⟨e, hbtw⟩ := hadj
  use e, hbtw.le hle

lemma reflAdj.le (h : G₁.reflAdj u w) (hle : G₁ ≤ G₂) : G₂.reflAdj u w := by
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
  bot := Edgeless ∅ β
  bot_le G := by refine ⟨?_, ?_, ?_⟩ <;> simp only [Edgeless, empty_subset, mem_empty_iff_false,
    false_iff, IsEmpty.forall_iff, implies_true]

instance instInhabitedGraph : Inhabited (Graph α β) where
  default := ⊥

@[simp]
lemma bot_V : (⊥ : Graph α β).V = ∅ := rfl

@[simp]
lemma bot_E : (⊥ : Graph α β).E = ∅ := rfl

@[simp]
lemma bot_incFun : (⊥ : Graph α β).incFun = 0 := rfl

@[simp]
lemma bot_inc : (⊥ : Graph α β).Inc = fun _ _ ↦ False := by
  ext e a
  simp only [instOrderBotGraph, Edgeless.E, not_inc_of_E_empty]

@[simp]
lemma vx_empty_iff_eq_bot : G.V = ∅ ↔ G = ⊥ := by
  constructor <;> rintro h
  · apply ext_inc
    · exact h
    · simp only [bot_E]
      by_contra! hE
      have := h ▸ (G.exists_vertex_inc hE.some_mem).choose_spec.vx_mem
      simp only [mem_empty_iff_false] at this
    · simp only [instOrderBotGraph, Edgeless.E, not_inc_of_E_empty, iff_false]
      rintro e v hinc
      have := h ▸ hinc.vx_mem
      simp only [mem_empty_iff_false] at this
  · rw [h]
    rfl

/-- If G₁ ≤ G₂ and G₂ is finite, then G₁ is finite too. -/
theorem finite_of_le_finite {G₁ G₂ : Graph α β} (hle : G₁ ≤ G₂) [h : G₂.Finite] : G₁.Finite := by
  constructor
  · -- Prove the vertex set is finite
    apply Set.Finite.subset h.vx_fin
    exact vx_subset_of_le hle
  · -- Prove the edge set is finite
    apply Set.Finite.subset h.edge_fin
    exact edge_subset_of_le hle

lemma vx_ncard_le_of_le [hfin : G₂.Finite] (hle : G₁ ≤ G₂) : G₁.V.ncard ≤ G₂.V.ncard :=
  Set.ncard_le_ncard (vx_subset_of_le hle) hfin.vx_fin

lemma edge_ncard_le_of_le [hfin : G₂.Finite] (hle : G₁ ≤ G₂) : G₁.E.ncard ≤ G₂.E.ncard :=
  Set.ncard_le_ncard (edge_subset_of_le hle) hfin.edge_fin

lemma vx_disjoint_of_disjoint {G₁ G₂ : Graph α β} (hDisj : Disjoint G₁ G₂) : Disjoint G₁.V G₂.V := by
  intro x hx1 hx2
  let G : Graph α β := Edgeless x β
  specialize hDisj (?_ : G ≤ G₁) ?_
  · exact ⟨hx1, (empty_subset _ : ∅ ⊆ _), by simp [G, Edgeless]⟩
  · exact ⟨hx2, (empty_subset _ : ∅ ⊆ _), by simp [G, Edgeless]⟩
  exact hDisj.1

-- Not True!
-- lemma Disjoint.edge_disjoint {G₁ G₂ : Graph α β} (hDisj : Disjoint G₁ G₂) : Disjoint G₁.E G₂.E := by

lemma le_of_exist_mutual_le (hle1 : G₁ ≤ G) (hle2 : G₂ ≤ G) : G₁ ≤ G₂ ↔ G₁.V ⊆ G₂.V ∧ G₁.E ⊆ G₂.E := by
  constructor
  · intro h
    exact ⟨vx_subset_of_le h, edge_subset_of_le h⟩
  · rintro ⟨hV, hE⟩
    refine ⟨hV, hE, ?_⟩
    rintro e he
    rw [incFun_eq_incFun_of_le hle1 he, incFun_eq_incFun_of_le hle2 (hE he)]

private lemma foo (U : Set α) : (∀ (x : α), G.Inc e x → x ∈ U) ↔ ∀ x ∈ (G.incFun e).support, x ∈ U := by
  simp_rw [Inc.iff_mem_support]

instance instForallIncDecidable (U : Set α) [DecidablePred (· ∈ U)] :
    Decidable (∀ x, G.Inc e x → x ∈ U) := decidable_of_iff _ (foo U).symm

/-- Induced subgraph -/
noncomputable def induce (G : Graph α β) (U : Set α) : Graph α β := by
  apply ofInc₂ U (G.E ∩ {e | ∀ (x : α), G.Inc e x → x ∈ U})
    (fun e x y ↦ G.Inc₂ e x y ∧ x ∈ U ∧ y ∈ U) (fun e x y ⟨hbtw, hx, hy⟩ ↦ ⟨hbtw.symm, hy, hx⟩)
    (fun e x y ⟨hbtw, hx, hy⟩ ↦ hx)
  · rintro e x y ⟨hbtw, hx, hy⟩
    simp only [mem_inter_iff, hbtw.edge_mem, mem_setOf_eq, true_and]
    rw [forall_inc_iff hbtw]
    exact ⟨hx, hy⟩
  · rintro e he
    obtain ⟨x, y, hbtw⟩ := G.exist_inc₂_of_mem he.1
    use x, y, hbtw
    rw [← forall_inc_iff hbtw]
    exact he.2
  · rintro e x y u v ⟨hxy, hx, hy⟩ ⟨huv, hu, hv⟩
    exact hxy.eq_or_eq_of_inc₂ huv

notation G "[" S "]" => Graph.induce G S

variable {U V U' V' : Set α}

@[simp]
noncomputable abbrev vxDel (G : Graph α β) (V : Set α) : Graph α β := G[G.V \ V]

noncomputable instance instHSub : HSub (Graph α β) (Set α) (Graph α β) where
  hSub := vxDel

@[simp]
lemma vxDel_notation : G[G.V \ U] = G - U := rfl

@[simp]
lemma induce_V : (G[U]).V = U := rfl

@[simp]
lemma vxDel_V : (G - U).V = G.V \ U := rfl

@[simp]
lemma induce_E : (G[U]).E = G.E ∩ {e | ∀ (x : α), G.Inc e x → x ∈ U} := rfl

@[simp]
lemma vxDel_E : (G - U).E = G.E ∩ {e | ∀ (x : α), G.Inc e x → x ∈ G.V \ U} := rfl

lemma induce_E_le (U : Set α) : (G[U]).E ⊆ G.E := by simp only [induce_E, inter_subset_left]

lemma vxDel_E_le (U : Set α) : (G - U).E ⊆ G.E := by simp only [vxDel_E, mem_diff,
  inter_subset_left]

@[simp]
lemma induce_inc₂_iff : (G[U]).Inc₂ e x y ↔ G.Inc₂ e x y ∧ x ∈ U ∧ y ∈ U :=
  Inc₂.ofInc₂

@[simp]
lemma vxDel_inc₂_iff : (G - U).Inc₂ e x y ↔ G.Inc₂ e x y ∧ x ∉ U ∧ y ∉ U := by
  simp +contextual only [← vxDel_notation, induce_inc₂_iff, mem_diff, iff_def,
    not_false_eq_true, and_self, implies_true, and_true, true_and, and_imp]
  rintro hbtw hx hy
  exact ⟨hbtw.vx_mem_left, hbtw.vx_mem_right⟩

lemma Inc₂.of_inc₂_induce (h : (G[U]).Inc₂ e x y) : G.Inc₂ e x y := by
  rw [induce_inc₂_iff] at h
  exact h.1

lemma Inc₂.of_inc₂_vxDel (h : (G - U).Inc₂ e x y) : G.Inc₂ e x y := by
  rw [vxDel_inc₂_iff] at h
  exact h.1

lemma Inc₂.iff_induce_pair : G.Inc₂ e x y ↔ G[{x, y}].Inc₂ e x y := by
  simp only [induce_inc₂_iff, mem_insert_iff, mem_singleton_iff, true_or, or_true, and_self,
    and_true]

@[simp]
lemma induce_inc_iff : (G[U]).Inc e v ↔ G.Inc e v ∧ ∀ (x : α), G.Inc e x → x ∈ U := by
  simp only [induce, Inc.ofInc₂]
  constructor
  · rintro ⟨u, hbtw, hv, hu⟩
    refine ⟨hbtw.inc_left, ?_⟩
    rw [forall_inc_iff hbtw]
    exact ⟨hv, hu⟩
  · rintro ⟨hinc, hU⟩
    obtain ⟨x, y, hx⟩ := G.exist_inc₂_of_mem hinc.edge_mem
    obtain rfl | rfl := hx.inc_iff.mp hinc
    · use y, hx, hU v hx.inc_left, hU y hx.inc_right
    · use x, hx.symm, hU v hx.inc_right, hU x hx.inc_left

@[simp]
lemma vxDel_inc_iff : (G - U).Inc e v ↔ G.Inc e v ∧ ∀ (x : α), G.Inc e x → x ∉ U := by
  simp +contextual only [← vxDel_notation, induce_inc_iff, mem_diff, iff_def, not_false_eq_true,
    implies_true, and_self, and_true, true_and, and_imp]
  rintro hinc hnin x hincx
  exact hincx.vx_mem

lemma Inc.of_Inc_induce (h : (G[U]).Inc e v) : G.Inc e v := by
  rw [induce_inc_iff] at h
  exact h.1

lemma Inc.of_Inc_vxDel (h : (G - U).Inc e v) : G.Inc e v := by
  rw [vxDel_inc_iff] at h
  exact h.1

@[simp]
lemma induce_isLoopAt_iff : (G[U]).IsLoopAt e x ↔ G.IsLoopAt e x ∧ ∀ (y : α), G.Inc e y → y ∈ U := by
  constructor
  · rintro hloop
    simp only [IsLoopAt_iff_inc₂, induce_inc₂_iff, and_self] at hloop ⊢
    obtain ⟨hbtw, hmem⟩ := hloop
    rw [forall_inc_iff hbtw]
    exact ⟨hbtw, hmem, hmem⟩
  · rintro ⟨hloop, hmem⟩
    rw [IsLoopAt_iff_inc₂] at hloop ⊢
    rw [forall_inc_iff hloop] at hmem
    simp [hloop, hmem]

@[simp]
lemma vxDel_isLoopAt_iff : (G - U).IsLoopAt e x ↔ G.IsLoopAt e x ∧ ∀ (y : α), G.Inc e y → y ∉ U := by
  simp only [← vxDel_notation]
  simp +contextual only [induce_isLoopAt_iff, mem_diff, iff_def, not_false_eq_true, implies_true,
    and_self, and_true, true_and, and_imp]
  rintro hloop hmem x hinc
  exact hinc.vx_mem

lemma IsLoopAt.of_IsLoopAt_induce (h : (G[U]).IsLoopAt e x) : G.IsLoopAt e x := by
  rw [induce_isLoopAt_iff] at h
  exact h.1

lemma IsLoopAt.of_IsLoopAt_vxDel (h : (G - U).IsLoopAt e x) : G.IsLoopAt e x := by
  rw [vxDel_isLoopAt_iff] at h
  exact h.1

theorem induce_le_induce (hle : G₁ ≤ G₂) (hsu : U ⊆ V) : G₁[U] ≤ G₂[V] := by
  rw [le_iff_inc]
  refine ⟨hsu, ?_, ?_⟩
  · rintro e he
    rw [induce_E] at he ⊢
    obtain ⟨he, hU⟩ := he
    refine ⟨hle.2.1 he, ?_⟩
    rintro x hinc₂
    rw [← Inc_iff_Inc_of_le hle he] at hinc₂
    exact hsu (hU x hinc₂)
  · rintro e he₁U v
    simp_rw [induce_inc_iff, ← Inc_iff_Inc_of_le hle he₁U.1]
    refine ⟨?_, ?_⟩
    · rintro ⟨hinc, hU⟩
      exact ⟨hinc, fun x a ↦ hsu (hU x a)⟩
    · rintro ⟨hinc, hU⟩
      exact And.imp_left (fun a ↦ hinc) he₁U

theorem vxDel_le_vxDel (hle : G₁ ≤ G₂) (hsu : U ⊆ V) : G₁ - V ≤ G₂ - U := by
  rw [← vxDel_notation]
  exact induce_le_induce hle <| diff_subset_diff hle.1 hsu

@[simp]
theorem induce_le_induce_iff_subset : G[U] ≤ G[V] ↔ U ⊆ V :=
  ⟨vx_subset_of_le, induce_le_induce (le_refl G)⟩

@[simp]
lemma vxDel_le_vxDel_iff_subset : G - U ≤ G - V ↔ G.V \ U ⊆ G.V \ V := by
  unfold instHSub vxDel
  simp only [induce_le_induce_iff_subset]

@[simp]
lemma vxDel_le_vxDel_iff_subset' (hU : U ⊆ G.V) (hV : V ⊆ G.V) : G - U ≤ G - V ↔ V ⊆ U := by
  rw [vxDel_le_vxDel_iff_subset]
  exact diff_subset_diff_iff_subset hU hV

@[simp]
theorem induce_eq_induce_iff : G[U] = G[V] ↔ U = V := by
  rw [le_antisymm_iff, induce_le_induce_iff_subset, induce_le_induce_iff_subset, antisymm_iff]

@[simp]
theorem vxDel_eq_vxDel_iff : G - U = G - V ↔ G.V \ U = G.V \ V := by
  rw [le_antisymm_iff, vxDel_le_vxDel_iff_subset, vxDel_le_vxDel_iff_subset, antisymm_iff]

@[simp]
theorem vxDel_eq_vxDel_iff' (hU : U ⊆ G.V) (hV : V ⊆ G.V) : G - U = G - V ↔ U = V := by
  rw [le_antisymm_iff, le_antisymm_iff, vxDel_le_vxDel_iff_subset' hU hV,
  vxDel_le_vxDel_iff_subset' hV hU, and_comm]
  rfl

@[simp]
lemma induce_le (G : Graph α β) (hU : U ⊆ G.V) : G[U] ≤ G := by
  rw [le_iff_inc]
  refine ⟨?_, ?_, ?_⟩ <;> simp +contextual only [induce_V, induce_E, mem_inter_iff, mem_setOf_eq,
    induce_inc_iff, implies_true, and_true, inter_subset_left, hU]

@[simp]
lemma vxDel_le (G : Graph α β) : G - U ≤ G := by
  rw [le_iff_inc]
  refine ⟨?_, ?_, ?_⟩ <;> simp +contextual only [vxDel_V, vxDel_E, mem_diff, inter_subset_left,
    mem_inter_iff, mem_setOf_eq, vxDel_inc_iff, not_false_eq_true, implies_true, and_true, diff_subset]

@[simp]
theorem induce_eq_self_iff : G[U] = G ↔ U = G.V := by
  constructor <;> intro h
  · rw [← h]
    rfl
  · simp only [le_antisymm_iff, induce_le G h.le, true_and]
    subst U
    rw [le_iff_inc]
    refine ⟨?_, ?_, ?_⟩
    · exact subset_refl _
    · intro e
      simp +contextual only [induce_E, mem_inter_iff, mem_setOf_eq, true_and]
      exact fun a x a ↦ a.vx_mem
    · simp +contextual only [induce_inc_iff, iff_self_and]
      rintro x e he hinc y hy
      exact hy.vx_mem

@[simp]
theorem vxDel_eq_self_iff : G - U = G ↔ Disjoint U G.V := by
  simp only [← vxDel_notation, induce_eq_self_iff, sdiff_eq_left, disjoint_comm]

@[simp]
lemma induce_V_eq_self  : G[G.V] = G := induce_eq_self_iff.mpr rfl

@[simp]
lemma vxDel_empty_eq_self : G - (∅ : Set α) = G := by
  simp only [vxDel_eq_self_iff, empty_disjoint]

@[simp]
lemma induce_empty_eq_bot : G[∅] = ⊥ := by
  rw [← vx_empty_iff_eq_bot]
  rfl

@[simp]
lemma vxDel_V_eq_bot : G - G.V = ⊥ := by
  simp only [← vxDel_notation, sdiff_self, bot_eq_empty, induce_empty_eq_bot, instOrderBotGraph]

@[simp]
lemma induce_mono (G : Graph α β) (hsu : U ⊆ V) : G[U] ≤ G[V] := by
  rwa [induce_le_induce_iff_subset]

lemma induce_monotone : Monotone (G[·] : Set α → Graph α β) := fun _U _V ↦ induce_mono G

@[simp]
lemma vxDel_anti (G : Graph α β) (hsu : U ⊆ V) : G - V ≤ G - U := by
  simp only [vxDel_le_vxDel_iff_subset]
  exact diff_subset_diff_right hsu

@[simp]
lemma vxDel_antitone (G : Graph α β) : Antitone (G - · : Set α → Graph α β) :=
  fun _U _V ↦ vxDel_anti G

@[simp]
lemma induce_idem (G : Graph α β) (U : Set α) : G[U][U] = G[U] := by
  simp only [induce_eq_self_iff, induce_V]

@[simp]
lemma vxDel_idem (G : Graph α β) (U : Set α) : G - U - U = G - U := by
  simp only [vxDel_eq_self_iff, vxDel_V]
  exact disjoint_sdiff_right

/-- If a vertex is in the induced subgraph, it's in the original graph and the inducing set. -/
@[simp]
lemma mem_induce_V_iff : v ∈ (G[U]).V ↔ v ∈ U := by rw [induce_V]

/-- Adjacency in induced subgraphs implies adjacency in the original graph. -/
lemma Adj.of_Adj_induce : (G[U]).Adj u v → G.Adj u v :=
  fun ⟨e, hBtw⟩ ↦ ⟨e, hBtw.of_inc₂_induce⟩

lemma Adj.of_Adj_vxDel : (G - U).Adj u v → G.Adj u v :=
  fun ⟨e, hBtw⟩ ↦ ⟨e, hBtw.of_inc₂_vxDel⟩

lemma reflAdj.of_reflAdj_induce_ne : (G[U]).reflAdj u v → u ≠ v → G.reflAdj u v := by
  rintro (hAdj | ⟨rfl, hmem⟩) hne
  · exact hAdj.of_Adj_induce.reflAdj
  · exact False.elim (hne rfl)

lemma reflAdj.of_reflAdj_induce_mem : (G[U]).reflAdj u v → u ∈ G.V → G.reflAdj u v := by
  rintro (hAdj | ⟨rfl, hmem⟩) hmem
  · exact hAdj.of_Adj_induce.reflAdj
  · exact reflAdj.refl hmem

lemma reflAdj.of_reflAdj_induce_subset : (G[U]).reflAdj u v → U ⊆ G.V → G.reflAdj u v := by
  rintro (hAdj | ⟨rfl, hmem⟩) hsubset
  · exact hAdj.of_Adj_induce.reflAdj
  · exact reflAdj.refl (hsubset hmem)

lemma reflAdj.of_reflAdj_vxDel : (G - U).reflAdj u v → G.reflAdj u v := by
  rintro (hAdj | ⟨rfl, hmem⟩)
  · exact hAdj.of_Adj_vxDel.reflAdj
  · exact reflAdj.refl hmem.1

theorem Connected.of_Connected_induce_mem : (G[U]).Connected u v → u ∈ G.V → G.Connected u v := by
  rintro h hmem
  induction h with
  | single hradj => exact reflAdj.connected <| hradj.of_reflAdj_induce_mem hmem
  | tail hconn hradj ih =>
    exact Relation.TransGen.tail ih <| hradj.of_reflAdj_induce_mem ih.mem_right

theorem Connected.of_Connected_induce_subset : (G[U]).Connected u v → U ⊆ G.V → G.Connected u v := by
  rintro h hsubset
  induction h with
  | single hradj => exact reflAdj.connected <| hradj.of_reflAdj_induce_subset hsubset
  | tail hconn hradj ih =>
    exact Relation.TransGen.tail ih <| hradj.of_reflAdj_induce_subset hsubset

theorem Connected.of_Connected_vxDel : (G - U).Connected u v → G.Connected u v := by
  rintro h
  induction h with
  | single hradj => exact reflAdj.connected hradj.of_reflAdj_vxDel
  | tail _hconn hradj ih => exact Relation.TransGen.tail ih hradj.of_reflAdj_vxDel

lemma Inc₂.induce_of_mem (hbtw : G.Inc₂ e u v) (hu : u ∈ U) (hv : v ∈ U) :
    G[U].Inc₂ e u v := by
  rw [induce_inc₂_iff]
  exact ⟨hbtw, hu, hv⟩

lemma Inc₂.vxDel_of_mem (hbtw : G.Inc₂ e u v) (hu : u ∉ U) (hv : v ∉ U) :
    (G - U).Inc₂ e u v := by
  rw [vxDel_inc₂_iff]
  exact ⟨hbtw, hu, hv⟩

lemma Inc.induce_of_mem (hinc : G.Inc e u) (hU : ∀ x, G.Inc e x → x ∈ U) :
    G[U].Inc e u := induce_inc_iff.mpr ⟨hinc, hU⟩

lemma Inc.vxDel_of_mem (hinc : G.Inc e u) (hU : ∀ x, G.Inc e x → x ∉ U) :
    (G - U).Inc e u := vxDel_inc_iff.mpr ⟨hinc, hU⟩

lemma Adj.induce_of_mem (hadj : G.Adj u v) (hU : ∀ x, G.reflAdj u x → x ∈ U) :
    G[U].Adj u v := by
  obtain ⟨e, hBtw⟩ := hadj
  have he : ∀ (x : α), G.Inc e x → x ∈ U := by
    rintro x hinc
    apply hU
    exact hBtw.inc_left.reflAdj_of_inc hinc
  use e
  rw [inc₂_iff_inc_and_loop]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [induce_inc_iff, hBtw.inc_left, true_and]
  · simpa only [induce_inc_iff, hBtw.inc_right, true_and]
  · rintro rfl
    rw [forall_inc_iff hBtw] at he
    rw [IsLoopAt_iff_inc₂, induce_inc₂_iff]
    exact ⟨hBtw, he⟩

lemma Adj.vxDel_of_mem (hadj : G.Adj u v) (hU : ∀ x, G.reflAdj u x → x ∉ U) :
    (G - U).Adj u v := by
  obtain ⟨e, hBtw⟩ := hadj
  use e
  simp only [vxDel_inc₂_iff, hBtw, true_and]
  use hU u <| reflAdj.refl hBtw.vx_mem_left, hU v hBtw.reflAdj

lemma reflAdj.induce_of_mem (hradj : G.reflAdj u v) (hU : ∀ x, G.reflAdj u x → x ∈ U) :
    G[U].reflAdj u v := by
  refine hradj.imp ?_ ?_
  · rintro hadj
    exact Adj.induce_of_mem hadj hU
  · rintro ⟨rfl, hu⟩
    use rfl, hU u hradj

lemma reflAdj.vxDel_of_mem (hradj : G.reflAdj u v) (hU : ∀ x, G.reflAdj u x → x ∉ U) :
    (G - U).reflAdj u v := by
  refine hradj.imp ?_ ?_
  · rintro hadj
    exact Adj.vxDel_of_mem hadj hU
  · rintro ⟨rfl, hu⟩
    use rfl, hu, hU u hradj

lemma Connected.induce_of_mem (h : G.Connected u v) (hU : ∀ x, G.Connected u x → x ∈ U) :
    G[U].Connected u v := by
  induction h with
  | single hradj =>
    refine reflAdj.connected <| hradj.induce_of_mem ?_
    rintro x hradj
    exact hU _ hradj.connected
  | tail hconn hradj ih =>
    refine Relation.TransGen.tail ih <| hradj.induce_of_mem ?_
    rintro x hxconn
    exact hU _ <| trans hconn hxconn.connected

lemma Connected.vxDel_of_mem (h : G.Connected u v) (hU : ∀ x, G.Connected u x → x ∉ U) :
    (G - U).Connected u v := by
  induction h with
  | single hradj =>
    refine reflAdj.connected <| hradj.vxDel_of_mem ?_
    rintro x hradj
    exact hU _ hradj.connected
  | tail hconn hradj ih =>
    refine Relation.TransGen.tail ih <| hradj.vxDel_of_mem ?_
    rintro x hxconn
    exact hU _ <| trans hconn hxconn.connected

lemma Isolated.induce_of_not_mem (hu : u ∉ G.V) : G[U].Isolated u := by
  intro e hinc
  simp only [induce_inc_iff] at hinc
  exact hu hinc.1.vx_mem

/-- A subgraph of a finite graph is also finite. -/
instance finite_of_finite_induce [h : G.Finite] (hU : Set.Finite U) : (G[U]).Finite := by
  refine ⟨hU, ?_⟩
  apply Set.Finite.subset h.edge_fin
  simp only [induce_E, inter_subset_left]

@[simp]
lemma vx_ncard_le_of_induce [hfin : G.Finite] (hU : U ⊆ G.V) : (G[U]).V.ncard ≤ G.V.ncard :=
  Set.ncard_le_ncard hU hfin.vx_fin

@[simp]
lemma edge_ncard_le_of_induce [hfin : G.Finite] : (G[U]).E.ncard ≤ G.E.ncard :=
  Set.ncard_le_ncard (G.induce_E_le U) hfin.edge_fin

/-- Restrict a graph to a set of edges -/
noncomputable def restrict (G : Graph α β) (R : Set β) : Graph α β where
  V := G.V
  E := G.E ∩ R
  incFun e :=
    haveI := Classical.dec (e ∈ R)
    if e ∈ R then G.incFun e else 0
  sum_eq e he := by
    simp only [he.2, ↓reduceIte]
    exact G.sum_eq he.1
  vertex_support e v h := by
    beta_reduce at h
    split_ifs at h with he
    · exact G.vertex_support h
    · simp only [Finsupp.coe_zero, Pi.zero_apply, ne_eq, not_true_eq_false] at h
  edge_support e v h := by
    beta_reduce at h
    split_ifs at h with he
    · exact ⟨G.edge_support h, he⟩
    · simp only [Finsupp.coe_zero, Pi.zero_apply, ne_eq, not_true_eq_false] at h

notation G "{" S "}" => Graph.restrict G S

@[simp]
noncomputable abbrev edgeDel (G : Graph α β) (F : Set β) : Graph α β := G{G.E \ F}

infix:70 " -ₑ " => Graph.edgeDel

variable {G H : Graph α β} {S S' R R'  : Set β}

@[simp]
theorem restrict_V : (G{R}).V = G.V := rfl

@[simp]
theorem edgeDel_V : (G -ₑ R).V = G.V := rfl

@[simp]
theorem restrict_E : (G{R}).E = G.E ∩ R := rfl

@[simp]
theorem edgeDel_E : (G -ₑ R).E = G.E \ R := by
  simp only [edgeDel, restrict_E, inter_eq_right, diff_subset]

@[simp]
theorem restrict_inc : (G{R}).Inc e v ↔ G.Inc e v ∧ e ∈ R := by
  unfold Inc
  simp [restrict]
  split_ifs with he <;> simp [he]

@[simp]
theorem edgeDel_inc : (G -ₑ R).Inc e v ↔ G.Inc e v ∧ e ∉ R := by
  simp only [edgeDel, restrict_inc, mem_diff, and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[simp]
lemma restrict_le (G : Graph α β) (R : Set β) : G{R} ≤ G := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [restrict, subset_refl, inter_subset_left, mem_inter_iff,
    ite_eq_left_iff, and_imp]
  tauto

@[simp]
lemma edgeDel_le (G : Graph α β) (R : Set β) : (G -ₑ R) ≤ G := by
  simp only [edgeDel, restrict_le]

@[simp]
lemma restrict_inc₂ : (G{R}).Inc₂ e x y ↔ G.Inc₂ e x y ∧ e ∈ R := by
  constructor
  · rintro hbtw
    refine ⟨?_, mem_of_mem_inter_right (restrict_E ▸ hbtw.edge_mem)⟩
    exact hbtw.le (restrict_le G R)
  · rintro ⟨hbtw, he⟩
    rwa [inc₂_iff_inc₂_of_edge_mem_le (restrict_le G R) ?_]
    simp only [restrict_E, mem_inter_iff, hbtw.edge_mem, he, and_self]

@[simp]
lemma edgeDel_inc₂ : (G -ₑ R).Inc₂ e x y ↔ G.Inc₂ e x y ∧ e ∉ R := by
  simp [edgeDel, restrict_inc₂]
  exact fun h _ ↦ h.edge_mem

/-- If an edge is in the restricted subgraph, it's in the original graph and the restricting set. -/
@[simp]
lemma mem_restrict_E_iff : e ∈ (G{R}).E ↔ e ∈ G.E ∧ e ∈ R := by
  simp only [restrict_E, mem_inter_iff]

@[simp]
lemma mem_edgeDel_E_iff : e ∈ (G -ₑ R).E ↔ e ∈ G.E ∧ e ∉ R := by
  simp only [edgeDel_E, mem_diff]

lemma restrict_le_restrict_of_le (hle : G₁ ≤ G₂) (hSR : S ⊆ R) : G₁{S} ≤ G₂{R} := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [restrict, vx_subset_of_le hle, subset_inter_iff, mem_inter_iff,
  and_imp]
  · refine ⟨?_, ?_⟩
    · rintro x ⟨H1, H2⟩
      exact edge_subset_of_le hle H1
    · rintro x ⟨H1, H2⟩
      exact hSR H2
  · rintro e he1 heS
    simp [heS]
    split_ifs with heR
    · exact incFun_eq_incFun_of_le hle he1
    · exact False.elim (heR (hSR heS))

lemma edgeDel_le_edgeDel_of_le (hle : G₁ ≤ G₂) (hSR : S ⊆ R) : G₁ -ₑ R ≤ G₂ -ₑ S :=
  restrict_le_restrict_of_le hle <| diff_subset_diff (edge_subset_of_le hle) hSR

@[simp]
lemma restrict_le_restrict_iff (G : Graph α β) (R S : Set β) :
    G{R} ≤ G{S} ↔ G.E ∩ R ⊆ G.E ∩ S := by
  refine ⟨edge_subset_of_le, ?_⟩
  rintro h
  refine ⟨subset_rfl, h, ?_⟩
  simp_rw [← inc_eq_inc_iff, funext_iff]
  simp +contextual only [restrict_E, mem_inter_iff, restrict_inc, and_true, eq_iff_iff,
    iff_self_and, and_imp]
  rintro e he hR v hinc
  simp [hR, (h ⟨he, hR⟩).2]

@[simp]
lemma edgeDel_le_edgeDel_iff (G : Graph α β) (R S : Set β) :
    G -ₑ R ≤ G -ₑ S ↔ G.E \ R ⊆ G.E \ S := by
  rw [restrict_le_restrict_iff, inter_eq_right.mpr diff_subset, inter_eq_right.mpr diff_subset]

@[simp]
lemma restrict_eq_restrict_iff (G : Graph α β) (R S : Set β) :
    G{R} = G{S} ↔ G.E ∩ R = G.E ∩ S := by
  rw [le_antisymm_iff, subset_antisymm_iff, restrict_le_restrict_iff, restrict_le_restrict_iff]

@[simp]
lemma edgeDel_eq_edgeDel_iff (G : Graph α β) (R S : Set β) :
    G -ₑ R = G -ₑ S ↔ G.E \ R = G.E \ S := by
  rw [le_antisymm_iff, subset_antisymm_iff, edgeDel_le_edgeDel_iff, edgeDel_le_edgeDel_iff]

@[simp]
lemma restrict_eq_self_iff (G : Graph α β) (R : Set β) : G{R} = G ↔ G.E ⊆ R := by
  constructor <;> intro h
  · rw [← h]
    simp only [restrict_E, inter_subset_right]
  · apply ext_inc
    · simp only [restrict]
    · simp only [restrict_E, inter_eq_left, h]
    · simp only [restrict_inc, and_iff_left_iff_imp]
      intro e v hinc
      exact h hinc.edge_mem

@[simp]
lemma edgeDel_eq_self_iff (G : Graph α β) (R : Set β) : G -ₑ R = G ↔ Disjoint G.E R := by
  rw [restrict_eq_self_iff, ← Set.subset_compl_iff_disjoint_right, diff_eq_compl_inter]
  simp only [subset_inter_iff, subset_refl, and_true]

@[simp]
lemma restrict_univ_eq_self : G{Set.univ} = G := by
  rw [restrict_eq_self_iff]
  exact subset_univ _

@[simp]
lemma edgeDel_univ_eq_self : G -ₑ Set.univ = Edgeless G.V β := by
  apply eq_Edgeless_of_E_empty
  simp only [edgeDel, diff_univ, restrict_E, inter_empty]

@[simp]
lemma restrict_E_eq_self : G{G.E} = G := by
  rw [restrict_eq_self_iff]

@[simp]
lemma edgeDel_E_eq_self : G -ₑ G.E = Edgeless G.V β := by
  apply eq_Edgeless_of_E_empty
  simp only [edgeDel, sdiff_self, bot_eq_empty, restrict_E, inter_empty]


lemma restrict_E_subset_singleton (e : β) : G{{e}}.E ⊆ {e} := by simp

lemma restrict_monotone (G : Graph α β) : Monotone (fun R ↦ G{R}) := by
  rintro R S h
  rw [restrict_le_restrict_iff]
  exact inter_subset_inter (fun ⦃a⦄ a ↦ a) h

@[simp]
lemma restrict_mono (G : Graph α β) (R S : Set β) (h : R ⊆ S) : G{R} ≤ G{S} :=
  restrict_monotone G h

lemma edgeDel_antitone (G : Graph α β) : Antitone (fun R ↦ G -ₑ R) := by
  rintro R S h
  rw [edgeDel_le_edgeDel_iff]
  exact diff_subset_diff_right h

@[simp]
lemma edgeDel_anti (G : Graph α β) (R S : Set β) (h : S ⊆ R) : G -ₑ R ≤ G -ₑ S :=
  edgeDel_antitone G h

@[simp]
lemma restrict_restrict_eq_restrict_inter (R S : Set β) : G{R}{S} = G{R ∩ S} := by
  apply ext_inc
  · simp only [restrict, inter_assoc, mem_inter_iff]
  · simp only [restrict, mem_inter_iff]
    rw [← inter_assoc]
  · intro e v
    simp only [restrict_inc, mem_inter_iff]
    rw [and_assoc]

@[simp]
lemma edgeDel_edgeDel_eq_edgeDel_union (R S : Set β) : (G -ₑ R) -ₑ S = G -ₑ (R ∪ S) := by
  simp only [edgeDel, restrict_E, restrict_restrict_eq_restrict_inter, restrict_eq_restrict_iff]
  tauto_set

@[simp]
lemma restrict_idem (R : Set β) : G{R}{R} = G{R} := by
  convert G.restrict_restrict_eq_restrict_inter R R
  simp only [inter_self]

@[simp]
lemma edgeDel_idem (R : Set β) : (G -ₑ R) -ₑ R = G -ₑ R := by
  convert G.edgeDel_edgeDel_eq_edgeDel_union R R
  simp only [union_self]

/-- Adjacency in restricted subgraphs implies adjacency in the original graph. -/
lemma Adj.of_Adj_restrict : (G{R}).Adj u v → G.Adj u v := (Adj.le · (restrict_le G R))

lemma Adj.of_Adj_edgeDel : (G -ₑ R).Adj u v → G.Adj u v := (Adj.le · (edgeDel_le G R))

/-- Connectedness in a restricted subgraph implies connectedness in the original graph. -/
lemma Connected.of_Connected_restrict : (G{R}).Connected u v → G.Connected u v :=
  (Connected.le · (restrict_le G R))

lemma Connected.of_Connected_edgeDel : (G -ₑ R).Connected u v → G.Connected u v :=
  (Connected.le · (edgeDel_le G R))

lemma reflAdj.restrict_of_le_reflAdj_restrict (hle : G₁ ≤ G₂)
    (hSradj : G₂{S}.reflAdj u v) (h : G₂.E ∩ S ⊆ G₁.E) (hu : u ∈ G₁.V) : G₁{S}.reflAdj u v := by
  have := restrict_le_restrict_of_le hle (Subset.rfl : S ⊆ S)
  refine hSradj.imp ?_ ?_
  · rintro ⟨e, hBtw⟩
    use e
    rwa [inc₂_iff_inc₂_of_edge_mem_le this ?_]
    · have he2S := hBtw.edge_mem
      exact ⟨h he2S, he2S.2⟩
  · simp only [restrict_V, and_imp]
    rintro rfl hu2
    use rfl

lemma Connected.restrict_of_le_inter_subset (hle : G₁ ≤ G₂) {S : Set β}
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
    exact ih.symm.mem_left

lemma restrict_Connected_iff_restrict_Connected_of_le (hle : G₁ ≤ G₂) {S : Set β}
    (h : G₂.E ∩ S ⊆ G₁.E) (hu : u ∈ G₁.V) :
    G₁{S}.Connected u v ↔ G₂{S}.Connected u v := by
  constructor <;> rintro hconn
  · refine Connected.le hconn ?_
    exact restrict_le_restrict_of_le hle fun ⦃a⦄ a ↦ a
  · exact Connected.restrict_of_le_inter_subset hle hconn h hu

/-- A restricted subgraph of a finite graph is also finite. -/
instance finite_of_finite_restrict {R : Set β} [h : G.Finite] : (G{R}).Finite := by
  constructor
  · -- Prove the vertex set is finite
    simp only [restrict_V]
    exact h.vx_fin
  · -- Prove the edge set is finite
    apply Set.Finite.subset h.edge_fin
    simp only [restrict_E, inter_subset_left]

instance finite_of_finite_edgeDel {R : Set β} [h : G.Finite] : (G -ₑ R).Finite :=
  finite_of_finite_restrict

@[simp]
lemma vx_ncard_le_of_restrict [hfin : G.Finite] : (G{R}).V.ncard ≤ G.V.ncard :=
  Set.ncard_le_ncard (vx_subset_of_le (restrict_le G R)) hfin.vx_fin

@[simp]
lemma vx_ncard_le_of_edgeDel [hfin : G.Finite] : (G -ₑ R).V.ncard ≤ G.V.ncard :=
  Set.ncard_le_ncard (vx_subset_of_le (edgeDel_le G R)) hfin.vx_fin

@[simp]
lemma edge_ncard_le_of_restrict [hfin : G.Finite] : (G{R}).E.ncard ≤ G.E.ncard :=
  Set.ncard_le_ncard (edge_subset_of_le (restrict_le G R)) hfin.edge_fin

@[simp]
lemma edge_ncard_le_of_edgeDel [hfin : G.Finite] : (G -ₑ R).E.ncard ≤ G.E.ncard :=
  Set.ncard_le_ncard (edge_subset_of_le (edgeDel_le G R)) hfin.edge_fin

@[simp]
lemma EdgeDel_singleton_inc₂_iff_inc₂_of_ne {e' : β} (hne : e ≠ e') :
    (G -ₑ {e}).Inc₂ e' u v ↔ G.Inc₂ e' u v := by
  refine ⟨fun h ↦ h.le (restrict_le G _), fun h ↦ by
    simp [restrict_inc₂, h, hne.symm, h.edge_mem]⟩

-- lemma IsLoopAt.reflAdj_iff_edgeDel_singleton (he : G.IsLoopAt e u) :
--     (G -ₑ {e}).reflAdj u v ↔ G.reflAdj u v := by
--   constructor <;> rintro h
--   · exact h.le (restrict_le G _)
--   · obtain ⟨e', hbtw⟩ | ⟨rfl, hu⟩ := h
--     · by_cases h' : e = e'
--       · subst e'
--         rw [hbtw.IsLoopAt_iff_eq] at he
--         subst v
--         exact reflAdj.refl hbtw.vx_mem_left
--       · apply Adj.reflAdj
--         use e'
--         rwa [EdgeDel_singleton_inc₂_iff_inc₂_of_ne h']
--     · exact reflAdj.of_vxMem hu

-- lemma IsLoopAt.connected_iff_edgeDel_singleton (he : G.IsLoopAt e u) :
--     (G -ₑ {e}).Connected u v ↔ G.Connected u v:= by
--   constructor <;> rintro h
--   · exact h.le (restrict_le G _)
--   · induction h with
--     | single hradj =>
--       apply reflAdj.connected
--       rwa [reflAdj_iff_edgeDel_singleton he]
--     | tail hconn hradj ih =>
--       apply ih.tail
--       rwa [reflAdj_iff_edgeDel_singleton he]

lemma induce_induce_eq_induce_restrict' (U V : Set α) : G[U][V] = G{G[U].E}[V] := by
  apply ext_inc
  · rfl
  · ext e
    simp +contextual only [induce_E, induce_inc_iff, and_imp, mem_inter_iff, mem_setOf_eq,
      restrict_E, restrict_inc, and_self_left, iff_def, implies_true, and_self, imp_self]
  · intro v e
    simp +contextual only [induce_inc_iff, and_imp, induce_E, restrict_inc, mem_inter_iff,
      mem_setOf_eq, iff_def, implies_true, and_self, and_true, true_and, forall_const, imp_self]
    exact fun a a_1 a_2 ↦ a.edge_mem

@[simp]
lemma induce_induce_eq_induce_restrict (U V : Set α) : G[U][V] = G{{e | ∀ (x : α), G.Inc e x → x ∈ U}}[V] := by
  rw [induce_induce_eq_induce_restrict' U V, induce_E]
  congr 1
  rw [restrict_eq_restrict_iff]
  simp

lemma induce_induce_eq_induce_left_iff (U V : Set α) : G[U][V] = G[U] ↔ U = V := by
  constructor
  · rintro h
    apply_fun (·.V) at h
    exact h.symm
  · rintro h
    subst V
    rw [induce_idem]

lemma vxDel_vxDel_eq_vxDel_left_iff (U V : Set α) : (G - U) - V = G - U ↔ G.V ∩ V ⊆ U := by
  simp only [vxDel_eq_self_iff, vxDel_V, subset_inter_iff, inter_subset_left, true_and]
  rw [← Set.subset_compl_iff_disjoint_left, Set.diff_subset_iff, Set.subset_union_compl_iff_inter_subset]

lemma induce_induce_eq_induce_right (U V : Set α) (h : G.V ∩ V ⊆ U) : G[U][V] = G[V] := by
  apply ext_inc
  · rfl
  · ext e
    simp +contextual only [induce_induce_eq_induce_restrict, induce_E, restrict_E, restrict_inc,
      mem_setOf_eq, and_imp, mem_inter_iff, iff_def, implies_true, and_self, true_and, and_true]
    rintro he hincV x hxinc
    exact h ⟨hxinc.vx_mem, hincV x hxinc⟩
  · intro e v
    simp +contextual only [induce_induce_eq_induce_restrict, induce_inc_iff, restrict_inc,
      mem_setOf_eq, and_imp, iff_def, implies_true, and_self, true_and, and_true]
    rintro hxinc hincV y hyinc
    exact h ⟨hyinc.vx_mem, hincV y hyinc⟩

lemma vxDel_vxDel_eq_vxDel_union (U V : Set α) : G - U - V = G - (U ∪ V) := by
  change (G[G.V \ U])[(G.V \ U) \ V] = G[G.V \ (U ∪ V)]
  rw [diff_diff]
  apply induce_induce_eq_induce_right
  tauto_set

lemma vxDel_comm (U V : Set α) : G - U - V = G - V - U := by
  rw [vxDel_vxDel_eq_vxDel_union, vxDel_vxDel_eq_vxDel_union, union_comm]

lemma vxDel_induce_eq_induce_vxDel (U V : Set α) : (G - U)[V] = G{(G - U).E}[V] := by
  rw [← vxDel_notation, induce_induce_eq_induce_restrict']

/-- G{R}[U] is the prefered notation for explicit subgraph over G[U]{R} -/
lemma induce_restrict_eq_restrict_induce (U : Set α) (R : Set β) : G[U]{R} = G{R}[U] := by
  apply ext_inc
  · simp only [restrict_V, induce_V]
  · ext e
    simp +contextual only [restrict_E, induce_E, mem_inter_iff, mem_setOf_eq, restrict_inc, and_imp,
      iff_def, and_self, imp_self, implies_true]
  · intro e v
    simp +contextual only [restrict_inc, induce_inc_iff, and_imp, iff_def, and_self, imp_self,
      implies_true]

/-- From here `subgraph` refers to G{R}[U] -/
@[simp]
theorem induce_restrict_eq_subgraph (U : Set α) (R : Set β) :
    G[U]{R} = G{R}[U] := G.induce_restrict_eq_restrict_induce U R

lemma vxDel_restrict_eq_restrict_vxDel (U : Set α) (R : Set β) :
    (G - U){R} = G{R} - U := by
  simp only [← vxDel_notation, restrict_V]
  rw [induce_restrict_eq_subgraph]

lemma subgraph_eq_induce (h : {e | e ∈ G.E ∧ ∀ (x : α), G.Inc e x → x ∈ U} ⊆ R) : G{R}[U] = G[U] := by
  apply ext_inc
  · rfl
  . simp only [induce_E, restrict_E, restrict_inc, and_imp]
    rw [inter_assoc]
    ext e
    simp +contextual only [mem_inter_iff, mem_setOf_eq, iff_def, implies_true, and_true, true_and]
    apply h
  · intro e v
    simp +contextual only [induce_inc_iff, restrict_inc, and_imp, iff_def, implies_true, and_self,
    true_and, and_true]
    rintro hinc hU
    exact h ⟨hinc.edge_mem, hU⟩

@[simp]
lemma induce_vxDel_eq_induce (U V : Set α) : G[U] - V = G[U \ V] := by
  rw [← vxDel_notation]
  simp
  apply subgraph_eq_induce
  intro e
  simp +contextual only [mem_diff, mem_setOf_eq, implies_true]

lemma subgraph_le (G : Graph α β) (R : Set β) {U : Set α} (hU : U ⊆ G.V) : G{R}[U] ≤ G :=
  (Graph.induce_le _ (by exact hU : U ⊆ G{R}.V)).trans (G.restrict_le R)

/-- Implicit subgraph iff explicit subgraph-/
theorem exists_subgraph_of_le (hle : G₁ ≤ G₂) : G₁ = G₂{G₁.E}[G₁.V] := by
  apply ext_inc
  · simp only [induce_V]
  · ext e
    simp +contextual only [induce_E, restrict_E, restrict_inc, and_imp, mem_inter_iff,
      mem_setOf_eq, iff_def, and_true, forall_const, implies_true]
    rintro he
    use edge_subset_of_le hle he
    obtain ⟨x, y, hBtw⟩ := exist_inc₂_of_mem (edge_subset_of_le hle he)
    rw [forall_inc_iff hBtw]
    rw [← inc₂_iff_inc₂_of_edge_mem_le hle he] at hBtw
    exact ⟨hBtw.vx_mem_left, hBtw.vx_mem_right⟩
  · intro e v
    simp +contextual only [induce_inc_iff, restrict_inc, and_imp, iff_def, forall_const]
    constructor
    · rintro hinc1
      use ⟨hinc1.le hle, hinc1.edge_mem⟩
      rintro x hinc2 hmem1
      rw [← Inc_iff_Inc_of_le hle hmem1] at hinc2
      exact hinc2.vx_mem
    · rintro h2inc h1e hforall
      exact (Inc_iff_Inc_of_le hle h1e).mpr h2inc

-- @[simp]
-- lemma induce_le_subgraph_iff : G[U'] ≤ G{R}[U] ↔ U' ⊆ U ∧ (∀ e ∈ G.E, (∀ u, G.Inc u e → u ∈ U') → e ∈ R) := by
--   constructor
--   · rintro h
--     refine ⟨h.1, fun e he h' ↦ ?_⟩
--     refine (h.2.1 (?_ : e ∈ G[U'].E)).1.2
--     simp only [induce_E, mem_inter_iff, mem_setOf_eq]
--     exact ⟨he, h'⟩
--   · rintro ⟨hU, hR⟩
--     refine ⟨hU, ?_, ?_⟩
--     · rintro e
--       simp +contextual only [induce_E, mem_inter_iff, mem_setOf_eq, restrict_E, restrict_inc,
--         and_imp, implies_true, hR e, and_self, forall_const, true_and]
--       rintro he h' x hxinc
--       exact hU (h' x hxinc)
--     · simp +contextual only [induce_E, mem_inter_iff, mem_setOf_eq, induce_inc_iff, implies_true,
--       and_true, restrict_inc, hR, iff_self_and, and_imp]
--       rintro v e he h hinc x hxinc
--       exact hU (h x hxinc)

lemma le_iff_of_mutual_le {G₁ G₂ G : Graph α β} (h1le : G₁ ≤ G) (h2le : G₂ ≤ G) : G₁ ≤ G₂ ↔
    G₁.V ⊆ G₂.V ∧ G₁.E ⊆ G₂.E := by
  constructor <;> rintro h
  · exact ⟨h.1, h.2.1⟩
  · rw [le_iff_inc]
    refine ⟨h.1, h.2, ?_⟩
    rintro e he v
    rw [Inc_iff_Inc_of_le h1le he, Inc_iff_Inc_of_le h2le (h.2 he)]


@[mk_iff]
structure IsVxSeparator (G : Graph α β) (u v : α) (S : Set α) : Prop where
  not_mem_left : u ∉ S
  not_mem_right : v ∉ S
  not_connected : ¬ (G [G.V \ S]).Connected u v

lemma not_exists_isSeparator_self (hu : u ∈ G.V) : ¬ ∃ S, G.IsVxSeparator u u S :=
  fun ⟨S, hS⟩ ↦ hS.not_connected <| Connected.refl <| by simp [hu, hS.not_mem_left]

-- lemma IsVxSeparator.iff_edgeDel_singleton_isLoop {S : Set α} (he : G.IsLoop e) :
--     G.IsVxSeparator u v S ↔ (G -ᴳ e).IsVxSeparator u v S := by
--   refine ⟨fun ⟨hu, hv, hconn⟩ ↦ ⟨hu, hv, ?_⟩, fun ⟨hu, hv, hconn⟩ ↦ ⟨hu, hv, ?_⟩⟩
--   · by_cases he' : e ∈ G[G.V \ S].E
--     · rw [restrict_V, ← induce_restrict_eq_subgraph]
--       rw [← IsLoop.connected_iff_edgeDel_singleton (e := e)] at hconn
--       convert hconn using 2
--       rw [restrict_eq_restrict_iff]
--       ext e
--       simp +contextual only [induce_E, mem_diff, mem_inter_iff, mem_setOf_eq, mem_singleton_iff,
--         and_self_left, and_congr_right_iff, true_and, implies_true]
--       rwa [IsLoop_iff_IsLoop_of_edge_mem_le (induce_le G diff_subset) he']
--     · rwa [restrict_V, subgraph_eq_induce]
--       rintro e'
--       simp +contextual only [mem_diff, mem_setOf_eq, mem_singleton_iff]
--       rintro hx
--       sorry
--   · sorry

def IsVxSetSeparator (G : Graph α β) (V S T : Set α) : Prop :=
  ∀ s ∈ S, ∀ t ∈ T, ¬ (G - V).Connected s t

namespace IsVxSetSeparator
variable {U V S S' T T' : Set α} (h : G.IsVxSetSeparator V S T)

def leftSet (h : G.IsVxSetSeparator V S T) : Set α :=
  {v | ∃ s ∈ S, (G - V).Connected v s}

def rightSet (h : G.IsVxSetSeparator V S T) : Set α :=
  {v | ∃ t ∈ T, (G - V).Connected v t}

lemma isVxSetSeparator_iff_inter_vxSet (G : Graph α β) {V S T : Set α} :
    G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V (S ∩ G.V) (T ∩ G.V) := sorry

@[simp]
lemma le (h : G₂.IsVxSetSeparator V S T) (hle : G₁ ≤ G₂) : G₁.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  refine h s hs t ht (hconn.le (induce_le_induce hle ?_))
  exact Set.diff_subset_diff_left hle.1

lemma symm (h : G.IsVxSetSeparator V S T) : G.IsVxSetSeparator V T S := by
  rintro s hs t ht hconn
  exact h t ht s hs hconn.symm

lemma comm : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V T S := ⟨symm, symm⟩

@[simp]
lemma subset (h : G.IsVxSetSeparator U S T) (hUV : U ⊆ V) : G.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  refine h s hs t ht (hconn.le (induce_le_induce (le_refl _) ?_))
  exact diff_subset_diff_right hUV

@[simp]
lemma subset_source (h : G.IsVxSetSeparator V S' T) (hS : S ⊆ S') : G.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  refine h s (hS hs) t ht (hconn.le (le_refl _))

@[simp]
lemma subset_target (h : G.IsVxSetSeparator V S T') (hT : T ⊆ T') : G.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  refine h s hs t (hT ht) (hconn.le (le_refl _))

@[simp]
lemma empty_iff : G.IsVxSetSeparator ∅ S T ↔ (∀ s ∈ S, ∀ t ∈ T, ¬ G.Connected s t) := by
  unfold IsVxSetSeparator
  simp only [vxDel_empty_eq_self]

@[simp]
lemma empty_source : G.IsVxSetSeparator V ∅ T := by
  rintro s hs t ht hconn
  rwa [mem_empty_iff_false] at hs

@[simp]
lemma empty_target : G.IsVxSetSeparator V S ∅ := by
  rintro s hs t ht hconn
  rwa [mem_empty_iff_false] at ht

@[simp]
lemma univ : G.IsVxSetSeparator univ S T := by
  rintro s hs t ht hconn
  simp only [vxDel_V, diff_univ, mem_empty_iff_false, not_false_eq_true,
    not_connected_of_not_mem] at hconn

@[simp]
lemma supp : G.IsVxSetSeparator G.V S T := by
  rintro s hs t ht hconn
  simp only [vxDel_V_eq_bot, instOrderBotGraph, Edgeless.V, mem_empty_iff_false, not_false_eq_true,
    not_connected_of_not_mem] at hconn

@[simp]
lemma source_subset (hSU : S ⊆ V) : G.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  have := hconn.mem_left
  simp only [vxDel_V, mem_diff, hSU hs, not_true_eq_false, and_false] at this

@[simp]
lemma target_subset (hTV : T ⊆ V) : G.IsVxSetSeparator V S T := by
  rintro s hs t ht hconn
  have := hconn.mem_right
  simp only [vxDel_V, mem_diff, hTV ht, not_true_eq_false, and_false] at this

@[simp]
lemma induce : (G - U).IsVxSetSeparator V S T ↔ G.IsVxSetSeparator (U ∪ V) S T := by
  unfold IsVxSetSeparator
  rw [vxDel_vxDel_eq_vxDel_union]

lemma iff_left_supported : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V (S ∩ G.V) T := by
  constructor <;> rintro h s hs t ht hconn
  · exact h s (mem_of_mem_inter_left hs) t ht hconn
  · by_cases h' : s ∈ G.V
    · exact h s (mem_inter hs h') t ht hconn
    · exact h' hconn.mem_left.1

lemma iff_right_supported : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V S (T ∩ G.V) := by
  constructor <;> rintro h s hs t ht hconn
  · exact h s hs t (mem_of_mem_inter_left ht) hconn
  · by_cases h' : t ∈ G.V
    · exact h s hs t (mem_inter ht h') hconn
    · exact h' hconn.mem_right.1

lemma iff_left_diff : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V (S \ V) T := by
  constructor <;> rintro h s hs t ht hconn
  · exact h s (mem_of_mem_diff hs) t ht hconn
  · exact h s ⟨hs, hconn.mem_left.2⟩ t ht hconn

lemma iff_right_diff : G.IsVxSetSeparator V S T ↔ G.IsVxSetSeparator V S (T \ V) := by
  constructor <;> rintro h s hs t ht hconn
  · exact h s hs t (mem_of_mem_diff ht) hconn
  · exact h s hs t ⟨ht, hconn.mem_right.2⟩ hconn

lemma source_inter_target_subset (h : G.IsVxSetSeparator V S T) : G.V ∩ S ∩ T ⊆ V := by
  rintro x hx
  specialize h x hx.1.2 x hx.2
  simpa only [Connected.refl_iff, vxDel_V, mem_diff, hx.1.1, true_and, not_not] using h

lemma leftSet_subset (h : G.IsVxSetSeparator V S T) : h.leftSet ⊆ G.V \ V :=
  fun _v ⟨_s, _hs, hconn⟩ ↦ hconn.mem_left

lemma subset_leftSet (h : G.IsVxSetSeparator V S T) (hS : S ⊆ G.V) : S ⊆ h.leftSet ∪ V := by
  rintro s hs
  by_cases h' : s ∈ V
  · exact Or.inr h'
  · left
    use s, hs
    exact Connected.refl ⟨hS hs, h'⟩

lemma rightSet_subset (h : G.IsVxSetSeparator V S T) : h.rightSet ⊆ G.V \ V :=
    fun _v ⟨_t, _ht, hconn⟩ ↦ hconn.mem_left

lemma subset_rightSet (h : G.IsVxSetSeparator V S T) (hT : T ⊆ G.V) : T ⊆ h.rightSet ∪ V := by
  rintro t ht
  by_cases h' : t ∈ V
  · exact Or.inr h'
  · left
    use t, ht
    exact Connected.refl ⟨hT ht, h'⟩

@[simp]
lemma symm_leftSet (h : G.IsVxSetSeparator V S T) : h.symm.leftSet = h.rightSet := by
  ext v
  simp only [IsVxSetSeparator.leftSet, IsVxSetSeparator.rightSet, mem_setOf_eq, exists_eq_right]

@[simp]
lemma symm_rightSet (h : G.IsVxSetSeparator V S T) : h.symm.rightSet = h.leftSet := by
  ext v
  simp only [IsVxSetSeparator.leftSet, IsVxSetSeparator.rightSet, mem_setOf_eq, exists_eq_right]

@[simp]
lemma leftSet_rightSet_disjoint (h : G.IsVxSetSeparator V S T) :
    _root_.Disjoint h.leftSet h.rightSet := by
  rintro U hUl hUr a haU
  obtain ⟨s, hs, hconn⟩ := hUl haU
  obtain ⟨t, ht, hconn'⟩ := hUr haU
  exact h s hs t ht (hconn.symm.trans hconn')

@[simp]
lemma leftSet_V_disjoint (h : G.IsVxSetSeparator V S T) : _root_.Disjoint h.leftSet V := by
  rintro U hUl hUV a haU
  obtain ⟨s, hs, hconn⟩ := hUl haU
  exact hconn.mem_left.2 (hUV haU)

@[simp]
lemma rightSet_V_disjoint (h : G.IsVxSetSeparator V S T) : _root_.Disjoint h.rightSet V := by
  rintro U hUr hUV a haU
  obtain ⟨t, ht, hconn⟩ := hUr haU
  exact hconn.mem_left.2 (hUV haU)

@[simp]
lemma leftSetV_inter_rightSetV (h : G.IsVxSetSeparator V S T) :
    (h.leftSet ∪ V) ∩ (h.rightSet ∪ V) = V := by
  ext a
  simp +contextual only [mem_inter_iff, mem_union, iff_def, and_imp, or_true, and_self,
    implies_true, and_true]
  rintro (hl | hl) (hr | hr) <;> try assumption
  have := h.leftSet_rightSet_disjoint (by simp [hl] : {a} ≤ _) (by simp [hr] : {a} ≤ _)
  simp only [bot_eq_empty, le_eq_subset, subset_empty_iff, singleton_ne_empty] at this

lemma leftSet_Sep_compl (h : G.IsVxSetSeparator V S T) :
    G.IsVxSetSeparator V h.leftSet (h.leftSet ∪ V)ᶜ := by
  rintro a ⟨s, hs, hconnas⟩ b hb hconn
  refine hb ?_
  left
  use s, hs, hconn.symm.trans hconnas

lemma rightSet_Sep_compl (h : G.IsVxSetSeparator V S T) :
    G.IsVxSetSeparator V h.rightSet (h.rightSet ∪ V)ᶜ := by
  rintro a ⟨t, ht, hconnat⟩ b hb hconn
  refine hb ?_
  left
  use t, ht, hconn.symm.trans hconnat

lemma compl_Sep_leftSet (h : G.IsVxSetSeparator V S T) :
    G.IsVxSetSeparator V (h.leftSet ∪ V)ᶜ h.leftSet := h.leftSet_Sep_compl.symm

lemma compl_Sep_rightSet (h : G.IsVxSetSeparator V S T) :
    G.IsVxSetSeparator V (h.rightSet ∪ V)ᶜ h.rightSet := h.rightSet_Sep_compl.symm

lemma leftSet_Sep_rightSet (h : G.IsVxSetSeparator V S T) :
    G.IsVxSetSeparator V h.leftSet h.rightSet := by
  refine h.leftSet_Sep_compl.subset_target ?_
  simp only [compl_union, subset_inter_iff]
  rw [subset_compl_iff_disjoint_left, subset_compl_iff_disjoint_left]
  exact ⟨h.leftSet_rightSet_disjoint, h.rightSet_V_disjoint.symm⟩

lemma mem_of_inc₂_leftSet (hbtw : G.Inc₂ e u v) (hu : u ∈ h.leftSet) :
    v ∈ h.leftSet ∪ V := by
  obtain ⟨s, hs, hconn⟩ := hu
  by_contra! hvV
  simp only [leftSet, mem_union, mem_setOf_eq, not_or, not_exists, not_and] at hvV
  obtain ⟨hnconn, hvV⟩ := hvV
  exact hnconn s hs
  <| (hbtw.induce_of_mem hconn.mem_left ⟨hbtw.vx_mem_right, hvV⟩).connected.symm.trans hconn

lemma mem_of_inc₂_rightSet (hbtw : G.Inc₂ e u v) (hv : v ∈ h.rightSet) :
    u ∈ h.rightSet ∪ V := by
  obtain ⟨t, ht, hconn⟩ := hv
  by_contra! huV
  simp only [rightSet, mem_union, mem_setOf_eq, not_or, not_exists, not_and] at huV
  obtain ⟨hnconn, huV⟩ := huV
  refine hnconn t ht <| hbtw.induce_of_mem (⟨hbtw.vx_mem_left, huV⟩ : u ∈ G.V \ V) hconn.mem_left
  |>.connected.trans hconn

/-- Given a set of edges, there is a separator that puts those edges on one side and the rest of
the edges on the other side. -/
def of_edges (G : Graph α β) (U : Set β) :
    G.IsVxSetSeparator {v | (∃ e ∈ U, G.Inc e v) ∧ ∃ e' ∉ U, G.Inc e' v}
    {v | ∃ e ∈ U, G.Inc e v} {v | ∃ e ∉ U, G.Inc e v} := by
  rintro s ⟨e, heU, hse⟩ t ⟨f, hfU, htf⟩ hconn
  sorry


end IsVxSetSeparator


def IsVxConnected (G : Graph α β) (n : ℕ) : Prop :=
  ∀ S : Finset α, S.card < n → (G[G.V \ S]).Conn

lemma IsVxConnected.one_of_conn [G.Conn] : G.IsVxConnected 1 := by
  simpa [IsVxConnected]

def IsEdgeConnected (G : Graph α β) (n : ℕ) : Prop :=
  ∀ U : Finset β, U.card < n → (G{Uᶜ}).Conn

lemma IsEdgeConnected.one_of_conn [G.Conn] : G.IsEdgeConnected 1 := by
  rintro S hS
  simp only [Nat.lt_one_iff, Finset.card_eq_zero] at hS
  subst S
  simp only [Finset.coe_empty, compl_empty, restrict_univ_eq_self]
  assumption
