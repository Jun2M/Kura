import Kura.Walk.Basic

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
  {W w w₀ w₁ w₂ P P₀ P₁ P₂ : WList α β} {S T X : Set α}

open WList Set

namespace Graph

/-! ### Trails -/

/-- `G.IsTrail w` means that `w` is a walk of `G` with no repeated edges. -/
@[mk_iff]
structure IsTrail (G : Graph α β) (W : WList α β) : Prop where
  isWalk : G.IsWalk W
  edge_nodup : W.edge.Nodup

lemma IsTrail.sublist (h : G.IsTrail w₂) (hle : w₁.IsSublist w₂) : G.IsTrail w₁ :=
  ⟨h.isWalk.sublist hle, hle.edge_sublist.nodup h.edge_nodup⟩

@[simp]
lemma nil_isTrail_iff : G.IsTrail (nil x) ↔ x ∈ V(G) := by
  simp [isTrail_iff]

@[simp]
lemma cons_isTrail_iff : G.IsTrail (cons x e w) ↔
    G.IsTrail w ∧ G.IsLink e x w.first ∧ e ∉ w.edge := by
  simp only [isTrail_iff, cons_isWalk_iff, cons_edge, List.nodup_cons]
  tauto

@[simp]
lemma IsTrail.of_cons (h : G.IsTrail (cons x e w)) : G.IsTrail w := by
  simp_all

lemma nil_isTrail (hx : x ∈ V(G)) : G.IsTrail (nil x) :=
  ⟨IsWalk.nil hx, by simp⟩

lemma IsTrail.reverse (h : G.IsTrail w) : G.IsTrail w.reverse :=
  ⟨h.isWalk.reverse, by simp [h.edge_nodup]⟩

@[simp]
lemma reverse_isTrail_iff : G.IsTrail (reverse w) ↔ G.IsTrail w :=
  ⟨fun h ↦ by simpa using h.reverse, IsTrail.reverse⟩

lemma IsTrail.of_le (hw : G.IsTrail w) (hle : G ≤ H) : H.IsTrail w :=
  ⟨hw.isWalk.of_le hle, hw.edge_nodup⟩

lemma IsTrail.vertexSet_subset (hw : G.IsTrail w) : V(w) ⊆ V(G) :=
  hw.isWalk.vertexSet_subset

lemma IsTrail.induce (hw : G.IsTrail w) (hX : V(w) ⊆ X) : G[X].IsTrail w :=
  ⟨hw.isWalk.induce hX, hw.edge_nodup⟩

/-- This is almost true without the `X ⊆ V(G)` assumption; the exception is where
`w` is a nil walk on a vertex in `X \ V(G)`. -/
lemma isTrail_induce_iff (hXV : X ⊆ V(G)) :
    (G.induce X).IsTrail w ↔ G.IsTrail w ∧ V(w) ⊆ X :=
  ⟨fun h ↦ ⟨h.of_le (G.induce_le hXV), h.vertexSet_subset⟩, fun h ↦ h.1.induce h.2⟩

lemma isTrail_induce_iff' (hw : w.Nonempty) : G[X].IsTrail w ↔ G.IsTrail w ∧ V(w) ⊆ X := by
  rw [isTrail_iff, isWalk_induce_iff' hw, and_assoc, isTrail_iff]
  tauto

@[simp]
lemma isTrail_vxDelete_iff : (G - X).IsTrail w ↔ G.IsTrail w ∧ Disjoint V(w) X := by
  rw [vxDelete_def, isTrail_induce_iff diff_subset, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.vertexSet_subset

lemma IsTrail.isTrail_le (h : G.IsTrail w) (hle : H ≤ G) (hE : E(w) ⊆ E(H))
    (hfirst : w.first ∈ V(H)) : H.IsTrail w where
  isWalk := h.isWalk.isWalk_le hle hE hfirst
  edge_nodup := h.edge_nodup

lemma IsTrail.isTrail_le_of_nonempty (h : G.IsTrail w) (hle : H ≤ G) (hE : E(w) ⊆ E(H))
    (hne : w.Nonempty) : H.IsTrail w where
  isWalk := h.isWalk.isWalk_le_of_nonempty hle hE hne
  edge_nodup := h.edge_nodup

lemma IsTrail.eq_append_cons_of_edge_mem (hW : G.IsTrail W) (heW : e ∈ W.edge) :
    ∃ W₁ W₂, G.IsTrail W₁ ∧ G.IsTrail W₂ ∧ e ∉ W₁.edge ∧ e ∉ W₂.edge ∧ W₁.edge.Disjoint W₂.edge ∧
    W = W₁ ++ WList.cons W₁.last e W₂ := by
  obtain ⟨W₁, W₂, hW₁, hW₂, heW₁, rfl⟩ := hW.isWalk.eq_append_cons_of_edge_mem heW
  have hnd := hW.edge_nodup
  simp only [append_edge, cons_edge, List.nodup_append, List.nodup_cons,
    List.disjoint_cons_right] at hnd
  use W₁, W₂
  simp_all [isTrail_iff]

lemma IsTrail.dInc_iff_eq_of_dInc (hW : G.IsTrail W) (he : W.DInc e u v) :
    W.DInc e x y ↔ (x = u) ∧ (y = v) := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction W with
  | nil u => simp at he
  | cons z f W IH =>
    rw [dInc_cons_iff] at h he
    obtain ⟨rfl, rfl, rfl⟩ | h := h
    · obtain ⟨rfl, he, rfl⟩ | he := he
      · simp
      simpa [he.edge_mem] using hW.edge_nodup
    obtain ⟨rfl, rfl, rfl⟩ | he := he
    · simpa [h.edge_mem] using hW.edge_nodup
    exact IH hW.of_cons he h

/-! ### Paths -/

/-- `G.IsPath P` means that `w` is a walk of `G` with no repeated vertices
(and therefore no repeated edges). -/
@[mk_iff]
structure IsPath (G : Graph α β) (w : WList α β) : Prop where
  isWalk : G.IsWalk w
  nodup : w.vx.Nodup

lemma nil_isPath (hx : x ∈ V(G)) : G.IsPath (nil x) :=
  ⟨IsWalk.nil hx, by simp⟩

@[simp] lemma nil_isPath_iff : G.IsPath (nil x) ↔ x ∈ V(G) := by
  simp [isPath_iff]

@[simp]
lemma cons_isPath_iff : G.IsPath (cons x e P) ↔ G.IsPath P ∧ G.IsLink e x P.first ∧ x ∉ P := by
  simp only [isPath_iff, cons_isWalk_iff, cons_vx, List.nodup_cons, mem_vx]
  tauto

@[simp]
lemma IsPath.of_cons (h : G.IsPath (cons x e P)) : G.IsPath P := by
  simp_all

lemma IsPath.isTrail (h : G.IsPath P) : G.IsTrail P where
  isWalk := h.1
  edge_nodup := by
    induction P with
    | nil u => simp
    | cons u e w ih =>
      simp_all only [cons_isPath_iff, cons_edge, List.nodup_cons, and_true, forall_const]
      exact fun he ↦ h.2.2 <| h.1.isWalk.vx_mem_of_edge_mem he h.2.1.inc_left

lemma IsPath.reverse (hp : G.IsPath P) : G.IsPath P.reverse where
  isWalk := hp.isWalk.reverse
  nodup := by simp [hp.nodup]

@[simp]
lemma reverse_isPath_iff : G.IsPath (reverse P) ↔ G.IsPath P :=
  ⟨fun h ↦ by simpa using h.reverse, IsPath.reverse⟩

lemma IsWalk.dedup_isPath [DecidableEq α] (h : G.IsWalk P) : G.IsPath P.dedup :=
  ⟨h.dedup, P.dedup_vx_nodup⟩

lemma IsLink.walk_isPath (h : G.IsLink e u v) (hne : u ≠ v) : G.IsPath h.walk :=
  ⟨h.walk_isWalk, by simp [hne]⟩

lemma IsPath.edge_nodup (h : G.IsPath P) : P.edge.Nodup :=
  h.isTrail.edge_nodup

lemma IsPath.of_le (hP : G.IsPath P) (hle : G ≤ H) : H.IsPath P :=
  ⟨hP.isWalk.of_le hle, hP.nodup⟩

lemma IsPath.vertexSet_subset (hP : G.IsPath P) : V(P) ⊆ V(G) :=
  hP.isWalk.vertexSet_subset

lemma IsPath.induce (hP : G.IsPath P) (hX : V(P) ⊆ X) : (G[X]).IsPath P :=
  ⟨hP.isWalk.induce hX, hP.nodup⟩

lemma IsPath.prefix (hP : G.IsPath P) (hP₀ : P₀.IsPrefix P) : G.IsPath P₀ where
  isWalk := hP.isWalk.prefix hP₀
  nodup := hP.nodup.sublist hP₀.vx_isPrefix.sublist

lemma IsPath.suffix (hP : G.IsPath P) (hP₀ : P₀.IsSuffix P) : G.IsPath P₀ where
  isWalk := hP.isWalk.suffix hP₀
  nodup := hP.nodup.sublist hP₀.vx_isSuffix.sublist

lemma IsPath.sublist (hP : G.IsPath P) (hP₀ : P₀.IsSublist P) : G.IsPath P₀ where
  isWalk := hP.isWalk.sublist hP₀
  nodup := hP.nodup.sublist hP₀.vx_sublist

/-- This is almost true without the `X ⊆ V(G)` assumption; the exception is where
`w` is a nil walk on a vertex in `X \ V(G)`. -/
lemma isPath_induce_iff (hXV : X ⊆ V(G)) : G[X].IsPath P ↔ G.IsPath P ∧ V(P) ⊆ X :=
  ⟨fun h ↦ ⟨h.of_le (G.induce_le hXV), h.vertexSet_subset⟩, fun h ↦ h.1.induce h.2⟩

lemma isPath_induce_iff' (hP : P.Nonempty) : G[X].IsPath P ↔ G.IsPath P ∧ V(P) ⊆ X := by
  rw [isPath_iff, isWalk_induce_iff' hP, and_assoc, isPath_iff]
  tauto

@[simp]
lemma isPath_vxDelete_iff : (G - X).IsPath P ↔ G.IsPath P ∧ Disjoint V(P) X := by
  rw [vxDelete_def, isPath_induce_iff diff_subset, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.vertexSet_subset

lemma IsPath.isPath_le (h : G.IsPath w) (hle : H ≤ G) (hE : E(w) ⊆ E(H))
    (hfirst : w.first ∈ V(H)) : H.IsPath w where
  isWalk := h.isWalk.isWalk_le hle hE hfirst
  nodup := h.nodup

lemma IsPath.isPath_le_of_nonempty (h : G.IsPath w) (hle : H ≤ G) (hE : E(w) ⊆ E(H))
    (hne : w.Nonempty) : H.IsPath w where
  isWalk := h.isWalk.isWalk_le_of_nonempty hle hE hne
  nodup := h.nodup

@[simp]
lemma isPath_edgeRestrict_iff {F : Set β} : (G ↾ F).IsPath P ↔ G.IsPath P ∧ E(P) ⊆ F := by
  simp [isPath_iff, and_right_comm]

@[simp]
lemma isPath_edgeDelete_iff {F : Set β} : (G ＼ F).IsPath P ↔ G.IsPath P ∧ Disjoint E(P) F := by
  rw [isPath_iff, isWalk_edgeDelete_iff, isPath_iff, and_right_comm]

lemma IsPath.append {P Q : WList α β} (hP : G.IsPath P) (hQ : G.IsPath Q) (hPQ : P.last = Q.first)
    (h_inter : ∀ x, x ∈ P → x ∈ Q → x = P.last) : G.IsPath (P ++ Q) := by
  induction P with
  | nil u => simpa
  | cons u e w ih =>
    simp_all only [mem_cons_iff, true_or, last_mem, or_true, implies_true, nonempty_prop,
      forall_const, cons_isPath_iff, first_mem, or_false, last_cons, forall_eq_or_imp, cons_append,
      append_first_of_eq, true_and]
    rw [← mem_vertexSet_iff, append_vertexSet hPQ, mem_union, not_or, mem_vertexSet_iff, mem_vertexSet_iff]
    refine ⟨hP.2.2, fun huQ ↦ ?_⟩
    rw [← h_inter.1 huQ] at hPQ
    exact hP.2.2 (by simp [← hPQ])

lemma IsPath.eq_append_cons_of_edge_mem (hP : G.IsPath P) (heP : e ∈ P.edge) :
    ∃ P₁ P₂, G.IsPath P₁ ∧ G.IsPath P₂ ∧ e ∉ P₁.edge ∧ e ∉ P₂.edge ∧
      P₁.vx.Disjoint P₂.vx ∧ P₁.edge.Disjoint P₂.edge ∧ P = P₁ ++ cons P₁.last e P₂ := by
  obtain ⟨P₁, P₂, hP₁, hP₂, heP₁, heP₂, hdj, rfl⟩ := hP.isTrail.eq_append_cons_of_edge_mem heP
  have hnd := hP.nodup
  rw [append_vx' rfl, List.nodup_append] at hnd
  simp only [cons_vx, List.tail_cons] at hnd
  use P₁, P₂
  simp_all [hdj, isPath_iff, hP₁.isWalk, hP₂.isWalk]

/-- An edge of a path `P` incident to the first vertex is the first edge.  -/
lemma IsPath.eq_firstEdge_of_isLink_first (hP : G.IsPath P) (heP : e ∈ P.edge)
    (he : G.Inc e P.first) : e = Nonempty.firstEdge P (by cases P with simp_all) := by
  obtain ⟨z, hex⟩ := he
  rw [← hP.isWalk.isLink_iff_isLink_of_mem heP] at hex
  exact hex.eq_firstEdge_of_isLink_first hP.nodup

@[simp] lemma IsPath.first_eq_last (h : G.IsPath w) : w.first = w.last ↔ w.Nil :=
  w.first_eq_last_iff h.nodup

/-! ### Fixed ends. (To be cleaned up) -/

@[mk_iff]
structure IsTrailFrom (G : Graph α β) (S T : Set α) (W : WList α β) : Prop extends
  G.IsTrail W, G.IsWalkFrom S T W

@[mk_iff]
structure IsPathFrom (G : Graph α β) (S T : Set α) (P : WList α β) :
  Prop extends G.IsPath P, G.IsWalkFrom S T P where
  eq_first_of_mem : ∀ ⦃x⦄, x ∈ P → x ∈ S → x = P.first
  eq_last_of_mem : ∀ ⦃y⦄, y ∈ P → y ∈ T → y = P.last

lemma IsPathFrom.isPath (h : G.IsPathFrom S T P) : G.IsPath P where
  isWalk := h.isWalk
  nodup := h.nodup

@[simp] lemma nil_isPathFrom : G.IsPathFrom S T (nil x) ↔ x ∈ V(G) ∧ x ∈ S ∧ x ∈ T := by
  simp [isPathFrom_iff]

lemma IsPathFrom.reverse (h : G.IsPathFrom S T w) : G.IsPathFrom T S w.reverse where
  isWalk := h.isWalk.reverse
  nodup := by simp [h.nodup]
  first_mem := by simp [h.last_mem]
  last_mem := by simp [h.first_mem]
  eq_first_of_mem x hx hxT := by simp [h.eq_last_of_mem (y := x) (by simpa using hx) hxT]
  eq_last_of_mem x hx hxS := by simp [h.eq_first_of_mem (x := x) (by simpa using hx) hxS]

lemma IsPathFrom.subset_left {S₀ : Set α} (hP : G.IsPathFrom S T P) (hS₀ : S₀ ⊆ S)
    (hx : P.first ∈ S₀) : G.IsPathFrom S₀ T P where
  isWalk := hP.isWalk
  nodup := hP.nodup
  first_mem := hx
  last_mem := hP.last_mem
  eq_first_of_mem _ hxP hxS₀ := hP.eq_first_of_mem hxP <| hS₀ hxS₀
  eq_last_of_mem := hP.eq_last_of_mem

lemma IsPathFrom.subset_right {T₀ : Set α} (hP : G.IsPathFrom S T P) (hT₀ : T₀ ⊆ T)
    (hx : P.last ∈ T₀) : G.IsPathFrom S T₀ P := by
  simpa using (hP.reverse.subset_left hT₀ (by simpa)).reverse

lemma IsPathFrom.of_le (h : H.IsPathFrom S T P) (hle : H ≤ G) : G.IsPathFrom S T P where
  isWalk := h.isWalk.of_le hle
  nodup := h.nodup
  first_mem := h.first_mem
  last_mem := h.last_mem
  eq_first_of_mem := h.eq_first_of_mem
  eq_last_of_mem := h.eq_last_of_mem

lemma IsPathFrom.isPathFrom_le (h : G.IsPathFrom S T P) (hle : H ≤ G) (hss : E(P) ⊆ E(H))
    (hne : P.first ∈ V(H)) : H.IsPathFrom S T P where
  isWalk := h.isWalk.isWalk_le hle hss hne
  nodup := h.nodup
  first_mem := h.first_mem
  last_mem := h.last_mem
  eq_first_of_mem := h.eq_first_of_mem
  eq_last_of_mem := h.eq_last_of_mem

lemma isPathFrom_cons : G.IsPathFrom S T (cons x e P) ↔
    x ∈ S ∧ x ∉ T ∧ G.IsLink e x P.first ∧ Disjoint S V(P) ∧ G.IsPathFrom {P.first} T P := by
  refine ⟨fun h ↦ ⟨h.first_mem, fun hxT ↦ ?_, ?_, disjoint_left.2 fun v hvS hv ↦ ?_, ?_⟩,
    fun ⟨hxS, hxT, hinc, hdj, h⟩ ↦ ?_⟩
  · obtain rfl : x = P.last := h.eq_last_of_mem (y := x) (by simp) hxT
    simpa using h.isPath.nodup
  · exact (cons_isPath_iff.1 h.isPath).2.1
  · obtain rfl : v = x := h.eq_first_of_mem (x := v) (by simp [mem_vertexSet_iff.1 hv]) hvS
    have hnd := h.isPath.nodup
    simp only [cons_vx, List.nodup_cons, mem_vx] at hnd
    exact hnd.1 hv
  · refine IsPathFrom.mk (h.isPath.suffix (by simp)) rfl (by simpa using h.last_mem) (by simp) ?_
    exact fun y hyP hyT ↦ h.eq_last_of_mem (by simp [hyP]) hyT
  have hxP : x ∉ P := hdj.not_mem_of_mem_left hxS
  refine IsPathFrom.mk (cons_isPath_iff.2 ⟨h.isPath, hinc, hxP⟩) (by simpa) h.last_mem ?_ ?_
  · simp only [mem_cons_iff, first_cons, forall_eq_or_imp, implies_true, true_and]
    exact fun a haP haS ↦ (hdj.not_mem_of_mem_left haS haP).elim
  simpa [hxT] using h.eq_last_of_mem

lemma IsPathFrom.not_mem_left_of_dInc (h : G.IsPathFrom S T P) (hP : P.DInc e x y) : y ∉ S :=
  fun hyS ↦ hP.ne_first h.nodup (h.eq_first_of_mem hP.vx_mem_right hyS)

lemma IsPathFrom.not_mem_right_of_dInc (h : G.IsPathFrom S T P) (hP : P.DInc e x y) : x ∉ T :=
  fun hyT ↦ hP.ne_last h.nodup (h.eq_last_of_mem hP.vx_mem_left hyT)

lemma IsTrailFrom.isTrail (h : G.IsTrailFrom S T w) : G.IsTrail w where
  isWalk := h.isWalk
  edge_nodup := h.edge_nodup

lemma IsTrailFrom.isWalkFrom (h : G.IsTrailFrom S T w) : G.IsWalkFrom S T w where
  isWalk := h.isWalk
  first_mem := h.first_mem
  last_mem := h.last_mem


lemma IsPathFrom.isWalkFrom (h : G.IsPathFrom S T w) : G.IsWalkFrom S T w where
  isWalk := h.isWalk
  first_mem := h.first_mem
  last_mem := h.last_mem

-- lemma IsPathFrom.isTrailFrom (h : G.IsPathFrom S T w) : G.IsTrailFrom S T w where
--   isWalk := h.isWalk
--   edge_nodup := h.isPath.isTrail.edge_nodup
--   first_mem := h.first_mem
--   last_mem := h.last_mem

-- lemma IsWalk.isTrail (hVd : G.IsWalk w) (hedge : w.edge.Nodup) : G.IsTrail w := ⟨hVd, hedge⟩

-- lemma IsWalk.isPath (hw : G.IsWalk w) (hvx : w.vx.Nodup) : G.IsPath w := ⟨hw, hvx⟩

lemma IsWalk.isWalkFrom (hVd : G.IsWalk w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsWalkFrom S T w := ⟨hVd, hfirst, hlast⟩

lemma IsWalk.isTrailFrom (hVd : G.IsWalk w) (hedge : w.edge.Nodup) (hfirst : w.first ∈ S)
    (hlast : w.last ∈ T) : G.IsTrailFrom S T w := ⟨⟨hVd, hedge⟩, hfirst, hlast⟩

lemma IsTrail.isPath (hT : G.IsTrail w) (hvx : w.vx.Nodup) : G.IsPath w := ⟨hT.isWalk, hvx⟩

lemma IsTrail.isTrailFrom (hT : G.IsTrail w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsTrailFrom S T w := ⟨hT, hfirst, hlast⟩

lemma nil_isWalkFrom (hx : x ∈ V(G)) (hxS : x ∈ S) (hxT : x ∈ T) : G.IsWalkFrom S T (nil x) :=
  ⟨IsWalk.nil hx, hxS, hxT⟩

@[simp] lemma nil_isWalkFrom_iff : G.IsWalkFrom S T (nil x) ↔ x ∈ V(G) ∧ x ∈ S ∧ x ∈ T := by
  simp [isWalkFrom_iff]

@[simp]
lemma cons_isTrailFrom : G.IsTrailFrom S T (cons x e w) ↔
    G.IsTrail w ∧ G.IsLink e x w.first ∧ e ∉ w.edge ∧ x ∈ S ∧ w.last ∈ T := by
  simp [isTrailFrom_iff, and_assoc]

-- @[simp]
-- lemma cons_isPathFrom : G.IsPathFrom S T (cons x e P) ↔
--     G.IsPath P ∧ G.IsLink e x P.first ∧ x ∉ P ∧ x ∈ S ∧ P.last ∈ T := by
--   simp [isPathFrom_iff, and_assoc]

@[simp]
lemma nil_isTrailFrom : G.IsTrailFrom S T (nil x) ↔ x ∈ V(G) ∧ x ∈ S ∧ x ∈ T := by
  simp [isTrailFrom_iff]

@[simp]
lemma IsPath.dropLast_vertexSet {w : WList α β} (hP : G.IsPath w) (hn : w.Nonempty) :
    V(w.dropLast) = V(w) \ {w.last} := by
  match w with
  | .nil x => simp at hn
  | .cons x e (.nil y) =>
    simp only [dropLast_cons_nil, nil_vertexSet, cons_vertexSet, pair_comm, last_cons, nil_last,
      mem_singleton_iff, insert_diff_of_mem]
    rw [diff_singleton_eq_self]
    rw [mem_singleton_iff]
    rintro rfl
    simp at hP
  | .cons x e (cons y e' w) =>
    have := dropLast_vertexSet (w := cons y e' w)
    simp only [cons_isPath_iff, cons_nonempty, cons_vertexSet, last_cons, forall_const, and_imp, first_cons,
      mem_cons_iff, not_or, dropLast_cons_cons] at this hP ⊢
    obtain ⟨⟨hP, h₂', hynin⟩, h₂, hne, hxnin⟩ := hP
    rw [this hP h₂' hynin, ← insert_diff_of_not_mem, insert_comm]
    simp only [mem_singleton_iff]
    rintro rfl
    simp only [last_mem, not_true_eq_false] at hxnin

@[simp]
lemma IsPath.last_not_mem_dropLast (hP : G.IsPath w) (hn : w.Nonempty) :
    w.last ∉ w.dropLast := by
  rintro h
  rw [← mem_vertexSet_iff, hP.dropLast_vertexSet hn] at h
  simp at h

end Graph

-- lemma append_left_isPath (h : w₁.last = w₂.first) (hP : G.IsPath (w₁ ++ w₂)) : G.IsPath w₁ where
--   validIn := hP.validIn.append_left_validIn h
--   nodup := by
--     have := hP.nodup
--     rw [append_vx' h] at this
--     exact this.of_append_left

-- lemma append_right_isPath (hP : G.IsPath (w₁ ++ w₂)) : G.IsPath w₂ where
--   validIn := hP.validIn.append_right_validIn
--   nodup := by
--     have := hP.nodup
--     rw [append_vx] at this
--     exact this.of_append_right

-- lemma not_mem_prefix_of_mem_suffix_tail (heq : w₁.last = w₂.first) (hP : G.IsPath (w₁ ++ w₂))
--     (hmem : u ∈ w₂.vx.tail) : u ∉ w₁.vx := by
--   have := hP.nodup
--   rw [append_vx' heq, nodup_append] at this
--   exact (this.2.2 · hmem)

-- lemma not_mem_suffix_of_mem_prefix_dropLast (hP : G.IsPath (w₁ ++ w₂))
-- (hmem : u ∈ w₁.vx.dropLast) :
--     u ∉ w₂.vx := by
--   have := hP.nodup
--   rw [append_vx, nodup_append] at this
--   exact this.2.2 hmem

-- lemma eq_first_of_mem_prefix_suffix (hP : G.IsPath (w₁ ++ w₂)) (heq : w₁.last = w₂.first)
--     (hmem1 : u ∈ w₁.vx) (hmem2 : u ∈ w₂.vx) : u = w₂.first := by
--   have := hP.nodup
--   rw [append_vx' heq, nodup_append] at this
--   have := this.2.2 hmem1
--   rw [← w₂.vx.head_cons_tail vx_ne_nil, mem_cons, ← first_eq_vx_head] at hmem2
--   simp_all only [imp_false, or_false]

-- lemma eq_last_of_mem_prefix_suffix (hP : G.IsPath (w₁ ++ w₂)) (heq : w₁.last = w₂.first)
--     (hmem1 : u ∈ w₁.vx) (hmem2 : u ∈ w₂.vx) : u = w₁.last :=
--   heq ▸ eq_first_of_mem_prefix_suffix hP heq hmem1 hmem2
