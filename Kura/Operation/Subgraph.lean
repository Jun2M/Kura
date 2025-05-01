import Kura.Connected

open Set Function

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v : α} {e f : β}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

/-! # Subgraph Operations

This file defines various operations to create subgraphs:
* `induce G U`: The subgraph induced by vertices in `U`
* `vxDel G U`: The subgraph with vertices in `U` removed (shorthand: `G - U`)
* `restrict G R`: The subgraph with only edges in `R`
* `edgeDel G R`: The subgraph with edges in `R` removed (shorthand: `G \ R`)
-/

-- section InternalHelpers

-- private lemma foo : (∀ (x : α), G.Inc e x → x ∈ U) ↔ ∀ x ∈ (G.IncFun e).support, x ∈ U := by
--   simp_rw [Inc.iff_mem_support]

-- instance instForallIncDecidable (U : Set α) [DecidablePred (· ∈ U)] :
--     Decidable (∀ x, G.Inc e x → x ∈ U) := decidable_of_iff _ foo.symm

-- end InternalHelpers

section CoreDefinitions
/-- Induced subgraph -/
def induce (G : Graph α β) (U : Set α) : Graph α β :=
  ofInc₂ U
  (fun e x y ↦ G.Inc₂ e x y ∧ x ∈ U ∧ y ∈ U)
  (fun _e _x _y ⟨hbtw, hx, hy⟩ ↦ ⟨hbtw.symm, hy, hx⟩)
  (fun _e _x _y ⟨_hbtw, hx, _hy⟩ ↦ hx)
  (fun _e _x _y _u _v ⟨hxy, _hx,_hy⟩ ⟨huv, _hu, _hv⟩ ↦ hxy.left_or_of_inc₂ huv)

notation G "[" S "]" => Graph.induce G S

/-- Basic properties of induced subgraph -/
@[simp] lemma induce_V : (G[U]).V = U := rfl

@[simp] lemma induce_E : (G[U]).E = {e | ∃ x y, G.Inc₂ e x y ∧ x ∈ U ∧ y ∈ U} := rfl

lemma induce_E_eq_inter : (G[U]).E = G.E ∩ {e | ∀ (x : α), G.Inc e x → x ∈ U} := by
  rw [induce_E]
  ext e
  simp only [mem_setOf_eq, mem_inter_iff]
  constructor
  · rintro ⟨x, y, hxy, hx, hy⟩
    refine ⟨hxy.edge_mem, fun z hinc ↦ ?_⟩
    obtain rfl | rfl := hxy.eq_of_inc hinc <;> assumption
  · rintro ⟨he, hinc⟩
    obtain ⟨x, y, hxy⟩ := Inc₂.exists_vx_inc₂ he
    exact ⟨x, y, hxy, hinc x hxy.inc_left, hinc y hxy.inc_right⟩

@[simp]
lemma induce_E_subset (U : Set α) : (G[U]).E ⊆ G.E := by
  rw [induce_E]
  exact fun e ⟨x, y, hxy, hx, hy⟩ ↦ hxy.edge_mem

@[simp] lemma induce_inc₂_iff : (G[U]).Inc₂ e x y ↔ G.Inc₂ e x y ∧ x ∈ U ∧ y ∈ U := by
  unfold induce
  rw [ofInc₂_inc₂]

lemma Inc₂.of_inc₂_induce (h : (G[U]).Inc₂ e x y) : G.Inc₂ e x y := by
  rw [induce_inc₂_iff] at h
  exact h.1

@[simp]
lemma induce_inc_iff : (G[U]).Inc e v ↔ G.Inc e v ∧ ∀ (x : α), G.Inc e x → x ∈ U := by
  simp only [induce, ofInc₂_inc]
  constructor
  · rintro ⟨u, hbtw, hv, hu⟩
    refine ⟨hbtw.inc_left, ?_⟩
    rw [forall_inc_iff hbtw]
    exact ⟨hv, hu⟩
  · rintro ⟨hinc, hU⟩
    obtain ⟨x, y, hx⟩ := Inc₂.exists_vx_inc₂ hinc.edge_mem
    obtain rfl | rfl := hx.inc_iff.mp hinc
    · use y, hx, hU x hx.inc_left, hU y hx.inc_right
    · use x, hx.symm, hU y hx.inc_right, hU x hx.inc_left

lemma Inc.of_Inc_induce (h : (G[U]).Inc e v) : G.Inc e v := by
  rw [induce_inc_iff] at h
  exact h.1

/-- Vertex deletion operator, defined as the induced subgraph on the complement of the deleted set -/
abbrev vxDel (G : Graph α β) (V : Set α) : Graph α β := G[G.V \ V]

instance instHSub : HSub (Graph α β) (Set α) (Graph α β) where
  hSub := vxDel

@[simp] lemma vxDel_notation : G[G.V \ U] = G - U := rfl

/-- Basic properties of vertex deletion -/
@[simp] lemma vxDel_V : (G - U).V = G.V \ U := rfl

lemma vxDel_V_subset (U : Set α) : (G - U).V ⊆ G.V := by simp only [vxDel_V, diff_subset]

@[simp]
lemma vxDel_E : (G - U).E = {e | ∃ x y, G.Inc₂ e x y ∧ x ∉ U ∧ y ∉ U} := by
  rw [← vxDel_notation, induce_E]
  ext e
  constructor
  · rintro ⟨x, y, hxy, hx, hy⟩
    use x, y, hxy, hx.2, hy.2
  · rintro ⟨x, y, hxy, hx, hy⟩
    use x, y, hxy, ⟨hxy.vx_mem_left, hx⟩
    exact ⟨hxy.vx_mem_right, hy⟩

-- @[simp] lemma vxDel_E : (G - U).E = G.E ∩ {e | ∀ (x : α), G.Inc e x → x ∈ G.V \ U} := rfl

lemma vxDel_E_subset (U : Set α) : (G - U).E ⊆ G.E := by
  rw [vxDel_E]
  exact fun e ⟨x, y, hxy, hx, hy⟩ ↦ hxy.edge_mem

@[simp]
lemma vxDel_inc₂_iff : (G - U).Inc₂ e x y ↔ G.Inc₂ e x y ∧ x ∉ U ∧ y ∉ U := by
  rw [← vxDel_notation, induce_inc₂_iff]
  simp +contextual only [← vxDel_notation, induce_inc₂_iff, mem_diff, iff_def,
    not_false_eq_true, and_self, implies_true, and_true, true_and, and_imp]
  rintro hbtw hx hy
  exact ⟨hbtw.vx_mem_left, hbtw.vx_mem_right⟩

lemma Inc₂.of_inc₂_vxDel (h : (G - U).Inc₂ e x y) : G.Inc₂ e x y := by
  rw [vxDel_inc₂_iff] at h
  exact h.1

@[simp]
lemma vxDel_inc_iff : (G - U).Inc e v ↔ G.Inc e v ∧ ∀ (x : α), G.Inc e x → x ∉ U := by
  simp +contextual only [← vxDel_notation, induce_inc_iff, mem_diff, iff_def, not_false_eq_true,
    implies_true, and_self, and_true, true_and, and_imp]
  rintro hinc hnin x hincx
  exact hincx.vx_mem

lemma Inc.of_Inc_vxDel (h : (G - U).Inc e v) : G.Inc e v := by
  rw [vxDel_inc_iff] at h
  exact h.1

/-- Restrict a graph to a set of edges -/
def restrict (G : Graph α β) (R : Set β) : Graph α β :=
  ofInc₂ G.V (fun e x y ↦ G.Inc₂ e x y ∧ e ∈ R)
  (fun _e _x _y ⟨hbtw, h⟩ ↦ ⟨hbtw.symm, h⟩)
  (fun _e _x _y ⟨hbtw, _h⟩ ↦ hbtw.vx_mem_left)
  (fun _e _x _y _u _v ⟨hxy, _he⟩ ⟨huv, _he⟩ ↦ hxy.left_or_of_inc₂ huv)

notation G "{" S "}" => Graph.restrict G S

/-- Basic properties of restricted graphs -/
@[simp] theorem restrict_V : (G{R}).V = G.V := rfl

@[simp] theorem restrict_E : (G{R}).E = G.E ∩ R := by
  rw [restrict, ofInc₂_E]
  ext e
  exact ⟨fun ⟨x, y, hxy, h⟩ ↦ ⟨hxy.edge_mem, h⟩, fun ⟨he, heR⟩ ↦ by simp [heR,
    Inc₂.exists_vx_inc₂ he]⟩

@[simp]
lemma restrict_E_subset : (G{R}).E ⊆ G.E := by
  rw [restrict_E]
  exact inter_subset_left

@[simp]
theorem restrict_inc : (G{R}).Inc e v ↔ G.Inc e v ∧ e ∈ R := by
  unfold Inc
  simp [restrict]

@[simp]
lemma mem_restrict_E_iff : e ∈ (G{R}).E ↔ e ∈ G.E ∧ e ∈ R := by
  simp only [restrict_E, mem_inter_iff]

@[simp] lemma restrict_inc₂_iff : (G{R}).Inc₂ e x y ↔ G.Inc₂ e x y ∧ e ∈ R := Iff.rfl

/-- Edge deletion operator, defined as the graph restricted to the complement of the deleted set -/
def edgeDel (G : Graph α β) (F : Set β) : Graph α β := G{G.E \ F}

scoped infix:70 " \\ " => Graph.edgeDel

@[simp] lemma edgeDel_notation : G{G.E \ F} = G \ F := rfl

/-- Basic properties of edge deletion -/
@[simp] theorem edgeDel_V : (G \ R).V = G.V := rfl

@[simp]
theorem edgeDel_E : (G \ R).E = G.E \ R := by
  rw [edgeDel, restrict_E, inter_eq_right]
  exact diff_subset

@[simp]
lemma edgeDel_E_subset : (G \ R).E ⊆ G.E := by
  rw [edgeDel_E]
  exact diff_subset

@[simp]
theorem edgeDel_inc : (G \ R).Inc e v ↔ G.Inc e v ∧ e ∉ R := by
  simp only [edgeDel, restrict_inc, mem_diff, and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[simp]
lemma mem_edgeDel_E_iff : e ∈ (G \ R).E ↔ e ∈ G.E ∧ e ∉ R := by
  simp only [edgeDel_E, mem_diff]

@[simp] lemma edgeDel_inc₂_iff : (G \ R).Inc₂ e x y ↔ G.Inc₂ e x y ∧ e ∉ R := by
  rw [edgeDel, restrict_inc₂_iff]
  simp +contextual only [mem_diff, and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

end CoreDefinitions

section Induce

/-! ## Induced Subgraphs

This section contains lemmas about the induced subgraph operation.
-/

/-- IsLoopAt properties -/
@[simp]
lemma induce_isLoopAt_iff : (G[U]).IsLoopAt e x ↔ G.IsLoopAt e x ∧ ∀ (y : α), G.Inc e y → y ∈ U := by
  constructor
  · rintro hloop
    simp only [inc₂_eq_iff_isLoopAt, induce_inc₂_iff, and_self] at hloop ⊢
    obtain ⟨hbtw, hmem, _⟩ := hloop
    rw [forall_inc_iff hbtw]
    exact ⟨hbtw, hmem, hmem⟩
  · rintro ⟨hloop, hmem⟩
    rw [← inc₂_eq_iff_isLoopAt] at hloop ⊢
    rw [forall_inc_iff hloop] at hmem
    simp [hloop, hmem]

lemma IsLoopAt.of_IsLoopAt_induce (h : (G[U]).IsLoopAt e x) : G.IsLoopAt e x := by
  rw [induce_isLoopAt_iff] at h
  exact h.1

/-- Order relation properties -/
@[simp]
lemma induce_le (G : Graph α β) (hU : U ⊆ G.V) : G[U] ≤ G := by
  rw [le_iff_inc₂]
  refine ⟨hU, fun e x y ↦ ?_⟩
  rw [induce_inc₂_iff]
  exact fun h ↦ h.left

theorem induce_le_induce_of_subset (hle : G ≤ G') (hsu : U ⊆ U') : G[U] ≤ G'[U'] := by
  rw [le_iff_inc₂]
  refine ⟨hsu, fun e x y ↦ ?_⟩
  rw [induce_inc₂_iff, induce_inc₂_iff]
  exact fun ⟨hbtw, hxU, hyU⟩ ↦ ⟨hbtw.of_le hle, hsu hxU, hsu hyU⟩

@[simp]
theorem induce_le_induce : G[U] ≤ G[U'] ↔ U ⊆ U' :=
  ⟨vx_subset_of_le, induce_le_induce_of_subset (le_refl G)⟩

@[simp]
theorem induce_eq_induce : G[U] = G[U'] ↔ U = U' := by
  rw [le_antisymm_iff, induce_le_induce, induce_le_induce, antisymm_iff]

@[simp]
theorem induce_eq_self_iff : G[U] = G ↔ U = G.V := by
  constructor <;> intro h
  · rw [← h]
    rfl
  · simp only [le_antisymm_iff, induce_le G h.le, true_and]
    subst U
    rw [le_iff_inc₂]
    refine ⟨subset_refl _, fun e x y hbtw ↦ ?_⟩
    rw [induce_inc₂_iff]
    exact ⟨hbtw, hbtw.vx_mem_left, hbtw.vx_mem_right⟩

@[simp]
lemma induce_V_eq_self  : G[G.V] = G := induce_eq_self_iff.mpr rfl

@[simp]
lemma induce_empty_eq_bot : G[∅] = ⊥ := by
  rw [← vx_empty_iff_eq_bot]
  rfl

@[simp]
lemma induce_mono (G : Graph α β) (hsu : U ⊆ U') : G[U] ≤ G[U'] := by
  rwa [induce_le_induce]

lemma induce_monotone : Monotone (G[·] : Set α → Graph α β) := fun _U _V ↦ induce_mono G

@[simp]
lemma induce_idem (G : Graph α β) (U : Set α) : G[U][U] = G[U] := by
  simp only [induce_eq_self_iff, induce_V]

/-- Adjacency properties -/
@[simp]
lemma mem_induce_V_iff : v ∈ (G[U]).V ↔ v ∈ U := by rw [induce_V]

lemma Inc₂.iff_induce_pair : G.Inc₂ e x y ↔ G[{x, y}].Inc₂ e x y := by
  simp only [induce_inc₂_iff, mem_insert_iff, mem_singleton_iff, true_or, or_true, and_self,
    and_true]

lemma Adj.of_Adj_induce : (G[U]).Adj u v → G.Adj u v :=
  fun ⟨e, hBtw⟩ ↦ ⟨e, hBtw.of_inc₂_induce⟩

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

/-- Connectivity properties -/
theorem Connected.of_Connected_induce_ne : (G[U]).Connected u v → u ≠ v → G.Connected u v := by
  rintro h hne
  induction h with
  | single hradj => exact reflAdj.connected <| hradj.of_reflAdj_induce_ne hne
  | tail hconn hradj ih =>
    expose_names
    by_cases hub : u = b
    · subst u
      exact hradj.of_reflAdj_induce_ne hne |>.connected
    · specialize ih hub
      exact ih.trans (hradj.of_reflAdj_induce_mem ih.mem_right |>.connected)

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

lemma SetConnected.of_induce (h : G[U].SetConnected S T) (hU : U ⊆ G.V) : G.SetConnected S T := by
  obtain ⟨s, hs, t, ht, h⟩ := h
  use s, hs, t, ht
  exact h.of_Connected_induce_subset hU

lemma SetConnected.of_induce_of_disjoint (h : G[U].SetConnected S T) (hU : Disjoint S T) :
    G.SetConnected S T := by
  obtain ⟨s, hs, t, ht, h⟩ := h
  use s, hs, t, ht
  refine h.of_Connected_induce_ne ?_
  rintro rfl
  have := hU (by simpa : {s} ⊆ S) (by simpa : {s} ⊆ T)
  simp at this

/-- Transfer of properties from original graph to subgraph -/
lemma Inc₂.induce_of_mem (hbtw : G.Inc₂ e u v) (hu : u ∈ U) (hv : v ∈ U) :
    G[U].Inc₂ e u v := by
  rw [induce_inc₂_iff]
  exact ⟨hbtw, hu, hv⟩

lemma Inc.induce_of_mem (hinc : G.Inc e u) (hU : ∀ x, G.Inc e x → x ∈ U) :
    G[U].Inc e u := induce_inc_iff.mpr ⟨hinc, hU⟩

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
    rw [← inc₂_eq_iff_isLoopAt, induce_inc₂_iff]
    exact ⟨hBtw, he⟩

lemma reflAdj.induce_of_mem (hradj : G.reflAdj u v) (hU : ∀ x, G.reflAdj u x → x ∈ U) :
    G[U].reflAdj u v := by
  refine hradj.imp ?_ ?_
  · rintro hadj
    exact Adj.induce_of_mem hadj hU
  · rintro ⟨rfl, hu⟩
    use rfl, hU u hradj

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

/-- Misc properties -/
lemma Isolated.induce_of_not_mem (hu : u ∉ G.V) : G[U].Isolated u := by
  intro e hinc
  simp only [induce_inc_iff] at hinc
  exact hu hinc.1.vx_mem

/-- Finiteness properties -/
instance finite_of_finite_induce [h : G.Finite] (hU : Set.Finite U) : (G[U]).Finite :=
  ⟨hU, h.edge_fin.subset <| induce_E_subset U⟩

@[simp]
lemma vx_ncard_le_of_induce [hfin : G.Finite] (hU : U ⊆ G.V) : (G[U]).V.ncard ≤ G.V.ncard :=
  Set.ncard_le_ncard hU hfin.vx_fin

@[simp]
lemma edge_ncard_le_of_induce [hfin : G.Finite] : (G[U]).E.ncard ≤ G.E.ncard :=
  Set.ncard_le_ncard (G.induce_E_subset U) hfin.edge_fin

end Induce

section VxDel

/-! ## Vertex Deletion

This section contains lemmas about the vertex deletion operation.
-/

/-- IsLoopAt properties -/
@[simp]
lemma vxDel_isLoopAt_iff : (G - U).IsLoopAt e x ↔ G.IsLoopAt e x ∧ ∀ (y : α), G.Inc e y → y ∉ U := by
  simp only [← vxDel_notation]
  simp +contextual only [induce_isLoopAt_iff, mem_diff, iff_def, not_false_eq_true, implies_true,
    and_self, and_true, true_and, and_imp]
  rintro hloop hmem x hinc
  exact hinc.vx_mem

lemma IsLoopAt.of_IsLoopAt_vxDel (h : (G - U).IsLoopAt e x) : G.IsLoopAt e x := by
  rw [vxDel_isLoopAt_iff] at h
  exact h.1

/-- Order relation properties -/
theorem vxDel_le_vxDel_of_subset (hle : G ≤ G') (hsu : U ⊆ U') : G - U' ≤ G' - U := by
  rw [← vxDel_notation]
  exact induce_le_induce_of_subset hle <| diff_subset_diff hle.1 hsu

@[simp]
lemma vxDel_le_vxDel : G - U ≤ G - U' ↔ G.V \ U ⊆ G.V \ U' := by
  unfold instHSub vxDel
  simp only [induce_le_induce]

@[simp]
lemma vxDel_le_vxDel_iff' (hU : U ⊆ G.V) (hU' : U' ⊆ G.V) : G - U ≤ G - U' ↔ U' ⊆ U := by
  rw [vxDel_le_vxDel]
  exact diff_subset_diff_iff_subset hU hU'

@[simp]
theorem vxDel_eq_vxDel_iff : G - U = G - U' ↔ G.V \ U = G.V \ U' := by
  rw [le_antisymm_iff, vxDel_le_vxDel, vxDel_le_vxDel, antisymm_iff]

@[simp]
theorem vxDel_eq_vxDel_iff' (hU : U ⊆ G.V) (hU' : U' ⊆ G.V) : G - U = G - U' ↔ U = U' := by
  rw [le_antisymm_iff, le_antisymm_iff, vxDel_le_vxDel_iff' hU hU',
  vxDel_le_vxDel_iff' hU' hU, and_comm]
  rfl

@[simp]
lemma vxDel_le (G : Graph α β) : G - U ≤ G := by
  rw [← vxDel_notation]
  exact induce_le G diff_subset

@[simp]
theorem vxDel_eq_self_iff : G - U = G ↔ Disjoint U G.V := by
  simp only [← vxDel_notation, induce_eq_self_iff, sdiff_eq_left, disjoint_comm]

@[simp]
lemma vxDel_empty_eq_self : G - (∅ : Set α) = G := by
  simp only [vxDel_eq_self_iff, empty_disjoint]

@[simp]
lemma vxDel_V_eq_bot : G - G.V = ⊥ := by
  simp only [← vxDel_notation, sdiff_self, bot_eq_empty, induce_empty_eq_bot, instOrderBotGraph]

@[simp]
lemma vxDel_univ_eq_bot : G - (Set.univ : Set α) = ⊥ := by
  rw [← vxDel_V_eq_bot, vxDel_eq_vxDel_iff]
  simp

@[simp]
lemma vxDel_anti (G : Graph α β) (hsu : U ⊆ U') : G - U' ≤ G - U := by
  simp only [vxDel_le_vxDel]
  exact diff_subset_diff_right hsu

@[simp]
lemma vxDel_antitone (G : Graph α β) : Antitone (G - · : Set α → Graph α β) :=
  fun _U _V ↦ vxDel_anti G

@[simp]
lemma vxDel_idem (G : Graph α β) (U : Set α) : G - U - U = G - U := by
  simp only [vxDel_eq_self_iff, vxDel_V]
  exact disjoint_sdiff_right

lemma vxDel_vxDel_eq_vxDel_left_iff (U V : Set α) : (G - U) - V = G - U ↔ G.V ∩ V ⊆ U := by
  simp only [vxDel_eq_self_iff, vxDel_V, subset_inter_iff, inter_subset_left, true_and]
  rw [← Set.subset_compl_iff_disjoint_left, Set.diff_subset_iff, Set.subset_union_compl_iff_inter_subset]

/-- Adjacency properties -/
lemma Adj.of_Adj_vxDel : (G - U).Adj u v → G.Adj u v :=
  fun ⟨e, hBtw⟩ ↦ ⟨e, hBtw.of_inc₂_vxDel⟩

lemma reflAdj.of_reflAdj_vxDel : (G - U).reflAdj u v → G.reflAdj u v := by
  rintro (hAdj | ⟨rfl, hmem⟩)
  · exact hAdj.of_Adj_vxDel.reflAdj
  · exact reflAdj.refl hmem.1

/-- Connectivity properties -/
theorem Connected.of_Connected_vxDel : (G - U).Connected u v → G.Connected u v := by
  rintro h
  induction h with
  | single hradj => exact reflAdj.connected hradj.of_reflAdj_vxDel
  | tail _hconn hradj ih => exact Relation.TransGen.tail ih hradj.of_reflAdj_vxDel

lemma SetConnected.of_vxDel (h : (G - U).SetConnected S T) : G.SetConnected S T := by
  obtain ⟨s, hs, t, ht, h⟩ := h
  use s, hs, t, ht
  exact h.of_Connected_vxDel

/-- Transfer of properties from original graph to subgraph -/
lemma Inc₂.vxDel_of_mem (hbtw : G.Inc₂ e u v) (hu : u ∉ U) (hv : v ∉ U) :
    (G - U).Inc₂ e u v := by
  rw [vxDel_inc₂_iff]
  exact ⟨hbtw, hu, hv⟩

lemma Inc.vxDel_of_mem (hinc : G.Inc e u) (hU : ∀ x, G.Inc e x → x ∉ U) :
    (G - U).Inc e u := vxDel_inc_iff.mpr ⟨hinc, hU⟩

lemma Adj.vxDel_of_mem (hadj : G.Adj u v) (hU : ∀ x, G.reflAdj u x → x ∉ U) :
    (G - U).Adj u v := by
  obtain ⟨e, hBtw⟩ := hadj
  use e
  simp only [vxDel_inc₂_iff, hBtw, true_and]
  use hU u <| reflAdj.refl hBtw.vx_mem_left, hU v hBtw.reflAdj

lemma reflAdj.vxDel_of_mem (hradj : G.reflAdj u v) (hU : ∀ x, G.reflAdj u x → x ∉ U) :
    (G - U).reflAdj u v := by
  refine hradj.imp ?_ ?_
  · rintro hadj
    exact Adj.vxDel_of_mem hadj hU
  · rintro ⟨rfl, hu⟩
    use rfl, hu, hU u hradj

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

end VxDel

section Restrict

/-! ## Edge Restriction

This section contains lemmas about the edge restriction operation.
-/

/-- Order relation properties -/
@[simp]
lemma restrict_le (G : Graph α β) (R : Set β) : G{R} ≤ G := by
  rw [le_iff_inc₂]
  exact ⟨subset_rfl, fun e x y hbtw ↦ hbtw.left⟩

lemma restrict_le_restrict_of_le (hle : G ≤ G') (hSR : F ⊆ R) : G{F} ≤ G'{R} := by
  rw [le_iff_inc₂]
  refine ⟨(vx_subset_of_le hle : G.V ⊆ G'.V), fun e x y hbtw ↦ ?_⟩
  use hbtw.left.of_le hle, hSR hbtw.right

@[simp]
lemma restrict_le_restrict_iff (G : Graph α β) (R S : Set β) :
    G{R} ≤ G{S} ↔ G.E ∩ R ⊆ G.E ∩ S := by
  refine ⟨fun h e he ↦ ?_, fun h ↦ ?_⟩
  · rw [mem_inter_iff, ← mem_restrict_E_iff] at he ⊢
    exact edge_mem_of_le h he
  · rw [le_iff_inc₂]
    refine ⟨subset_rfl, fun e x y hbtw ↦ ?_⟩
    rw [restrict_inc₂_iff] at hbtw ⊢
    exact ⟨hbtw.1, (h ⟨hbtw.1.edge_mem, hbtw.2⟩).2⟩

@[simp]
lemma restrict_eq_restrict_iff (G : Graph α β) (R S : Set β) :
    G{R} = G{S} ↔ G.E ∩ R = G.E ∩ S := by
  rw [le_antisymm_iff, subset_antisymm_iff, restrict_le_restrict_iff, restrict_le_restrict_iff]

/-- Equality to self/base cases -/
@[simp]
lemma restrict_eq_self_iff (G : Graph α β) (R : Set β) : G{R} = G ↔ G.E ⊆ R := by
  constructor <;> intro h
  · rw [← h]
    simp only [restrict_E, inter_subset_right]
  · refine le_antisymm (restrict_le G R) ?_
    rw [le_of_exist_mutual_le le_rfl (restrict_le G R)]
    exact ⟨subset_rfl, fun e he ↦ by simp [he, h he]⟩

@[simp]
lemma restrict_univ_eq_self : G{Set.univ} = G := by
  rw [restrict_eq_self_iff]
  exact subset_univ _

@[simp]
lemma restrict_E_eq_self : G{G.E} = G := by
  rw [restrict_eq_self_iff]

/-- Monotonicity -/
lemma restrict_monotone (G : Graph α β) : Monotone (fun R ↦ G{R}) := by
  rintro R S h
  rw [restrict_le_restrict_iff]
  exact inter_subset_inter (fun ⦃a⦄ a ↦ a) h

@[simp]
lemma restrict_mono (G : Graph α β) {R S : Set β} (h : R ⊆ S) : G{R} ≤ G{S} :=
  restrict_monotone G h

/-- Interaction (Self) -/
@[simp]
lemma restrict_restrict_eq_restrict_inter (R S : Set β) : G{R}{S} = G{R ∩ S} := by
  apply ext_inc
  · simp only [restrict_V]
  · simp +contextual only [restrict_inc, mem_inter_iff, iff_def, and_self, implies_true]

@[simp]
lemma restrict_idem (R : Set β) : G{R}{R} = G{R} := by
  convert G.restrict_restrict_eq_restrict_inter R R
  simp only [inter_self]

/-- Adjacency properties -/
lemma Adj.of_Adj_restrict : (G{R}).Adj u v → G.Adj u v := Adj.of_le (restrict_le G R)

lemma reflAdj.restrict_of_le_reflAdj_restrict (hSradj : G'{F}.reflAdj u v)  (hle : G ≤ G')
    (h : G'.E ∩ F ⊆ G.E) (hu : u ∈ G.V) : G{F}.reflAdj u v := by
  have := restrict_le_restrict_of_le hle (Subset.rfl : F ⊆ F)
  refine hSradj.imp ?_ ?_
  · rintro ⟨e, hBtw⟩
    use e
    rwa [inc₂_eq_inc₂_of_edge_mem_and_inc₂_le_inc₂ ?_ (Inc₂.le_of_le this)]
    · have he2S := hBtw.edge_mem
      rw [restrict_E] at he2S ⊢
      exact ⟨h he2S, he2S.2⟩
  · simp only [restrict_V, and_imp]
    rintro rfl hu2
    use rfl

/-- Connectivity properties -/
lemma Connected.of_Connected_restrict : (G{R}).Connected u v → G.Connected u v :=
  (Connected.of_le · (restrict_le G R))

lemma Connected.restrict_of_le_inter_subset (hFconn : G'{F}.Connected u v) (hle : G ≤ G')
    (h : G'.E ∩ F ⊆ G.E) (hu : u ∈ G.V) : G{F}.Connected u v := by
  induction hFconn with
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

lemma restrict_Connected_iff_restrict_Connected_of_le (hle : G ≤ G')
    (h : G'.E ∩ F ⊆ G.E) (hu : u ∈ G.V) :
    G{F}.Connected u v ↔ G'{F}.Connected u v := by
  constructor <;> rintro hconn
  · exact hconn.of_le <| restrict_le_restrict_of_le hle fun ⦃a⦄ a ↦ a
  · exact hconn.restrict_of_le_inter_subset hle h hu

/- SetConnected lemmas -/
-- No specific lemmas in the original file

/-- Transfer of properties from original graph to subgraph -/
lemma Inc₂.restrict_of_mem (hinc : G.Inc₂ e u v) (hU : e ∈ R) : (G{R}).Inc₂ e u v := by
  rw [restrict_inc₂_iff]
  exact ⟨hinc, hU⟩

lemma Inc.restrict_of_mem (hinc : G.Inc e u) (hU : e ∈ R) : (G{R}).Inc e u := by
  rw [restrict_inc]
  exact ⟨hinc, hU⟩

/-- Finiteness & Cardinality -/
instance finite_of_finite_restrict {R : Set β} [h : G.Finite] : (G{R}).Finite := by
  constructor
  · -- Prove the vertex set is finite
    simp only [restrict_V]
    exact h.vx_fin
  · -- Prove the edge set is finite
    apply Set.Finite.subset h.edge_fin
    simp only [restrict_E, inter_subset_left]

@[simp]
lemma vx_ncard_le_of_restrict [hfin : G.Finite] : (G{R}).V.ncard ≤ G.V.ncard :=
  Set.ncard_le_ncard (vx_subset_of_le (restrict_le G R)) hfin.vx_fin

@[simp]
lemma edge_ncard_le_of_restrict [hfin : G.Finite] : (G{R}).E.ncard ≤ G.E.ncard :=
  Set.ncard_le_ncard (edge_subset_of_le (restrict_le G R)) hfin.edge_fin

/-- Specific edge cases -/
lemma restrict_E_subset_singleton (e : β) : G{{e}}.E ⊆ {e} := by simp

end Restrict

section EdgeDel

/-! ## Edge Deletion

This section contains lemmas about the edge deletion operation.
-/

/-- Order relation properties -/
@[simp]
lemma edgeDel_le (G : Graph α β) (R : Set β) : (G \ R) ≤ G := by
  simp only [edgeDel, restrict_le]

lemma edgeDel_le_edgeDel_of_subset (hle : G ≤ G') (hRF : R ⊆ F) : G \ F ≤ G' \ R :=
  restrict_le_restrict_of_le hle <| diff_subset_diff (edge_subset_of_le hle) hRF

@[simp]
lemma edgeDel_le_edgeDel (G : Graph α β) (R S : Set β) :
    G \ R ≤ G \ S ↔ G.E \ R ⊆ G.E \ S := by
  rw [edgeDel, edgeDel, restrict_le_restrict_iff, inter_eq_right.mpr diff_subset,
  inter_eq_right.mpr diff_subset]

@[simp]
lemma edgeDel_eq_edgeDel_iff (G : Graph α β) (R S : Set β) :
    G \ R = G \ S ↔ G.E \ R = G.E \ S := by
  rw [le_antisymm_iff, subset_antisymm_iff, edgeDel_le_edgeDel, edgeDel_le_edgeDel]

/-- Equality to self/base cases -/
@[simp]
lemma edgeDel_eq_self_iff (G : Graph α β) (R : Set β) : G \ R = G ↔ Disjoint G.E R := by
  rw [edgeDel, restrict_eq_self_iff, ← Set.subset_compl_iff_disjoint_right, diff_eq_compl_inter]
  simp only [subset_inter_iff, subset_refl, and_true]

@[simp]
lemma edgeDel_univ_eq_self : G \ Set.univ = Edgeless G.V β := by
  rw [← edgeDel_V, ← edge_empty_iff_eq_Edgeless]
  simp only [edgeDel, diff_univ, restrict_E, inter_empty]

@[simp]
lemma edgeDel_E_eq_self : G \ G.E = Edgeless G.V β := by
  rw [← edgeDel_V, ← edge_empty_iff_eq_Edgeless]
  simp only [edgeDel, diff_self, bot_eq_empty, restrict_E, inter_empty]

@[simp]
lemma edgeDel_empty_eq_self : G \ ∅ = G := by
  rw [edgeDel_eq_self_iff]
  simp

/-- Antitonicity -/
lemma edgeDel_antitone (G : Graph α β) : Antitone (fun R ↦ G \ R) := by
  rintro R S h
  rw [edgeDel_le_edgeDel]
  exact diff_subset_diff_right h

@[simp]
lemma edgeDel_anti (G : Graph α β) (R S : Set β) (h : S ⊆ R) : G \ R ≤ G \ S :=
  edgeDel_antitone G h

/-- Interaction (Self) -/
@[simp]
lemma edgeDel_edgeDel_eq_edgeDel_union (R S : Set β) : (G \ R) \ S = G \ (R ∪ S) := by
  simp only [edgeDel, restrict_E, restrict_restrict_eq_restrict_inter, restrict_eq_restrict_iff]
  tauto_set

@[simp]
lemma edgeDel_idem (R : Set β) : (G \ R) \ R = G \ R := by
  convert G.edgeDel_edgeDel_eq_edgeDel_union R R
  simp only [union_self]

/-- Inc₂ lemmas -/
@[simp]
lemma edgeDel_inc₂ : (G \ R).Inc₂ e x y ↔ G.Inc₂ e x y ∧ e ∉ R := by
  rw [edgeDel, restrict_inc₂_iff, mem_diff, and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

/-- Adjacency properties -/
lemma Adj.of_Adj_edgeDel : (G \ R).Adj u v → G.Adj u v := Adj.of_le (edgeDel_le G R)

/-- Connectivity properties -/
lemma Connected.of_Connected_edgeDel : (G \ R).Connected u v → G.Connected u v :=
  (Connected.of_le · (edgeDel_le G R))

lemma SetConnected.of_Connected_edgeDel : (G \ R).SetConnected S T → G.SetConnected S T := by
  rintro h
  obtain ⟨s, hs, t, ht, h⟩ := h
  use s, hs, t, ht
  exact h.of_Connected_edgeDel

/-- Transfer of properties from original graph to subgraph -/
lemma Inc₂.edgeDel_of_mem (hinc : G.Inc₂ e u v) (hU : e ∉ R) : (G \ R).Inc₂ e u v := by
  rw [edgeDel_inc₂_iff]
  exact ⟨hinc, hU⟩

lemma Inc.edgeDel_of_mem (hinc : G.Inc e u) (hU : e ∉ R) : (G \ R).Inc e u := by
  rw [edgeDel_inc]
  exact ⟨hinc, hU⟩

/-- Finiteness & Cardinality -/
instance finite_of_finite_edgeDel {R : Set β} [h : G.Finite] : (G \ R).Finite :=
  finite_of_finite_restrict

@[simp]
lemma vx_ncard_le_of_edgeDel [hfin : G.Finite] : (G \ R).V.ncard ≤ G.V.ncard :=
  Set.ncard_le_ncard (vx_subset_of_le (edgeDel_le G R)) hfin.vx_fin

@[simp]
lemma edge_ncard_le_of_edgeDel [hfin : G.Finite] : (G \ R).E.ncard ≤ G.E.ncard :=
  Set.ncard_le_ncard (edge_subset_of_le (edgeDel_le G R)) hfin.edge_fin

/-- Specific edge cases (Singleton Deletion) -/
@[simp]
lemma EdgeDel_singleton_inc₂_iff_inc₂_of_ne {e' : β} (hne : e ≠ e') :
    (G \ {e}).Inc₂ e' u v ↔ G.Inc₂ e' u v := by
  refine ⟨fun h ↦ h.of_le (edgeDel_le G _), fun h ↦ by
    simp [edgeDel_inc₂, h, hne.symm, h.edge_mem]⟩

end EdgeDel

section MixedOperations

/-! ## Mixed Operations

This section contains lemmas about interactions between different subgraph operations.
-/

/-- Induce-induce interactions -/
lemma induce_induce_eq_induce_restrict' (U V : Set α) : G[U][V] = G{G[U].E}[V] := by
  apply ext_inc₂
  · rfl
  · simp only [induce_inc₂_iff, induce_E, restrict_inc₂_iff, mem_setOf_eq, and_congr_left_iff,
    and_congr_right_iff, and_imp]
    rintro e x y hxV hyV hbtw
    refine ⟨fun ⟨hxU, hyU⟩ ↦ ?_, fun ⟨u, v, a, huU, hvU⟩ ↦ ?_⟩
    · use x, y
    · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hbtw.eq_or_eq_of_inc₂ a <;> tauto

@[simp]
lemma induce_induce_eq_induce_restrict (U V : Set α) :
    G[U][V] = G{G.E ∩ {e | ∀ (x : α), G.Inc e x → x ∈ U}}[V] := by
  rw [induce_induce_eq_induce_restrict' U V, induce_E_eq_inter]

lemma induce_induce_eq_induce_left_iff (U V : Set α) : G[U][V] = G[U] ↔ U = V := by
  constructor
  · rintro h
    apply_fun (·.V) at h
    exact h.symm
  · rintro h
    subst V
    rw [induce_idem]

lemma induce_induce_eq_induce_right (U V : Set α) (h : G.V ∩ V ⊆ U) : G[U][V] = G[V] := by
  apply ext_inc
  · rfl
  · rintro e v
    simp only [induce_induce_eq_induce_restrict, induce_inc_iff, restrict_inc, mem_inter_iff,
      mem_setOf_eq, and_imp]
    refine ⟨fun ⟨⟨hinc, he, hallU⟩, hallV⟩ ↦ ?_, fun ⟨hinc, hallV⟩ ↦ ?_⟩
    · use hinc, fun x hincx ↦ hallV x hincx he hallU
    · use ⟨hinc, hinc.edge_mem, fun z hz ↦ h ⟨hz.vx_mem, hallV z hz⟩⟩, fun a b _ _ ↦ hallV a b

lemma vxDel_vxDel_eq_vxDel_union (U V : Set α) : G - U - V = G - (U ∪ V) := by
  change (G[G.V \ U])[(G.V \ U) \ V] = G[G.V \ (U ∪ V)]
  rw [diff_diff]
  apply induce_induce_eq_induce_right
  tauto_set

lemma vxDel_comm (U V : Set α) : G - U - V = G - V - U := by
  rw [vxDel_vxDel_eq_vxDel_union, vxDel_vxDel_eq_vxDel_union, union_comm]

/-- Mixed induce/restrict interactions -/
@[simp]
lemma induce_restrict_eq_restrict_induce (U : Set α) (R : Set β) : G[U]{R} = G{R}[U] := by
  apply ext_inc
  · simp only [restrict_V, induce_V]
  · intro e v
    simp +contextual only [restrict_inc, induce_inc_iff, and_imp, iff_def, implies_true, and_self,
    true_and, and_true]

lemma restrict_induce_eq_induce (h : {e | e ∈ G.E ∧ ∀ (x : α), G.Inc e x → x ∈ U} ⊆ R) :
    G{R}[U] = G[U] := by
  apply ext_inc
  · rfl
  · intro e v
    simp +contextual only [induce_inc_iff, restrict_inc, and_imp, iff_def, implies_true, and_self,
    true_and, and_true]
    rintro hinc hU
    exact h ⟨hinc.edge_mem, hU⟩

/-- Mixed induce/vxDel interactions -/
lemma vxDel_induce_eq (U V : Set α) : (G - U)[V] = G{(G - U).E}[V] := by
  rw [← vxDel_notation, induce_induce_eq_induce_restrict']

@[simp]
lemma induce_vxDel_eq_induce (U V : Set α) : G[U] - V = G[U \ V] := by
  rw [← vxDel_notation]
  simp
  apply restrict_induce_eq_induce
  intro e
  simp +contextual only [mem_diff, mem_setOf_eq, mem_inter_iff, implies_true, and_self]

/-- vxDel/restrict interactions -/
lemma vxDel_restrict_eq_restrict_vxDel (U : Set α) (R : Set β) :
    (G - U){R} = G{R} - U := by
  simp only [← vxDel_notation, restrict_V]
  rw [induce_restrict_eq_restrict_induce]

/-- vxDel/edgeDel interactions -/
lemma vxDel_edgeDel_comm : (G - U) \ R = G \ R - U := by
  rw [eq_comm, edgeDel, ← vxDel_restrict_eq_restrict_vxDel, edgeDel, restrict_eq_restrict_iff]
  have := G.vxDel_E_subset U
  tauto_set

/-- General mixed interactions -/
lemma restrict_induce_le (G : Graph α β) (R : Set β) (hU : U ⊆ G.V) : G{R}[U] ≤ G :=
  (Graph.induce_le _ (by exact hU : U ⊆ G{R}.V)).trans (G.restrict_le R)



lemma exists_compatible_of_le (h : H ≤ G) : ∃ H' : Graph α β, H.Compatible H' ∧ H ∪ H' = G := by
  use G \ H.E, fun e heH he ↦ by simp [heH] at he, le_antisymm ?_ ?_
  · rw [le_of_exist_mutual_le (union_le h (edgeDel_le G H.E)) le_rfl]
    simp [h]
  · rw [le_iff_inc₂]
    simp only [union_vxSet, edgeDel_V, subset_union_right, true_and]
    rintro e u v hbtw
    rw [union_inc₂_iff, inc₂_iff_inc₂_edge_mem_of_le h]
    refine (em (e ∈ H.E)).imp ?_ ?_ <;> simp [hbtw]



end MixedOperations

section SubgraphRelations

/-! ## General Subgraph Relations

This section contains lemmas relating the subgraph operations back to general graph subgraphs.
-/

/-- Implicit subgraph iff explicit subgraph-/
theorem exists_subgraph_of_le (hle : G ≤ G') : G = G'{G.E}[G.V] := by
  apply ext_inc
  · simp only [induce_V]
  · intro e v
    simp +contextual only [induce_inc_iff, restrict_inc, and_imp, iff_def, forall_const]
    constructor
    · rintro hinc1
      use ⟨hinc1.le hle, hinc1.edge_mem⟩
      rintro x hinc2 hmem1
      rw [← Inc_eq_Inc_of_le hle hmem1] at hinc2
      exact hinc2.vx_mem
    · rintro h2inc h1e hforall
      exact (Inc_eq_Inc_of_le hle h1e) ▸ h2inc

/-- For determining when graphs are ordered based on vertex and edge subsets -/
lemma le_iff_of_mutual_le {G₁ G₂ G : Graph α β} (h1le : G₁ ≤ G) (h2le : G₂ ≤ G) : G₁ ≤ G₂ ↔
    G₁.V ⊆ G₂.V ∧ G₁.E ⊆ G₂.E := by
  constructor <;> rintro h
  · exact ⟨vx_subset_of_le h, edge_subset_of_le h⟩
  · rw [le_iff_inc]
    refine ⟨h.1, h.2, ?_⟩
    rintro e he v
    rw [Inc_eq_Inc_of_le h1le he, Inc_eq_Inc_of_le h2le (h.2 he)]

end SubgraphRelations

end Graph
