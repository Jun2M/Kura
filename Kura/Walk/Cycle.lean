import Kura.Walk.Path
import Kura.Operation.Subgraph

/-
This file defined predicates stating that an abstract walk `w` is a closed walk/tour/cycle of a
graph `G`.

The definitions of closed walk and tour are very simple, and intuitive.
On the other hand, the definition of cycle is a bit complicated. `w.vx.tail.Nodup` is not enough:
This allows `[a]` (a point walk) to be a cycle, and `[a, e, b, e, a]` (a backtrack) to be a cycle.

I think it is good to allow a point walk to be a closed walk and a tour, so that it is true that
a graph with a single vertex is an even graph and therefore has an eulerian tour.
Whereas for a cycle, in terms of graphic matroid, we don't want an empty set to be a dependent set
in every graph with at least one vertex.
-/

variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ : WList α β}

namespace Graph

open WList List Set

/-- `G.IsClosedWalk w` means that `w` is a closed walk of `G`. -/
@[mk_iff]
structure IsClosedWalk (G : Graph α β) (w : WList α β) : Prop where
  isWalk : G.IsWalk w
  first_last : w.first = w.last

/-- `G.IsTour w` means that `w` is a tour of `G`. -/
@[mk_iff]
structure IsTour (G : Graph α β) (w : WList α β) : Prop extends G.IsClosedWalk w, G.IsTrail w

/-- `G.IsCycle w` means that `w` is a cycle of `G`. -/
@[mk_iff]
structure IsCycle (G : Graph α β) (w : WList α β) : Prop extends G.IsTour w where
  nonempty : w.Nonempty
  nodup : w.vx.tail.Nodup


lemma IsWalk.isClosedWalk (hVd : G.IsWalk w) (hfirst : w.first = w.last) : G.IsClosedWalk w :=
  ⟨hVd, hfirst⟩

lemma IsWalk.isTour (hVd : G.IsWalk w) (hfirst : w.first = w.last) (hedge : w.edge.Nodup) :
    G.IsTour w := ⟨⟨hVd, hfirst⟩, hedge⟩

lemma IsWalk.isCycle (hVd : G.IsWalk w) (hfirst : w.first = w.last) (hedge : w.edge.Nodup)
    (hnonempty : w.Nonempty) (hvx : w.vx.tail.Nodup) : G.IsCycle w :=
  ⟨⟨⟨hVd, hfirst⟩, hedge⟩, hnonempty, hvx⟩

lemma IsClosedWalk.isCycle (h : G.IsClosedWalk w) (hedge : w.edge.Nodup) (hnonempty : w.Nonempty)
    (hvx : w.vx.tail.Nodup) : G.IsCycle w := ⟨⟨h, hedge⟩, hnonempty, hvx⟩

lemma IsClosedWalk.isTour (h : G.IsClosedWalk w) (hedge : w.edge.Nodup) : G.IsTour w :=
  ⟨h, hedge⟩

lemma IsTour.isCycle (hT : G.IsTour w) (hnonempty : w.Nonempty) (hvx : w.vx.tail.Nodup) :
    G.IsCycle w := ⟨hT, hnonempty, hvx⟩

@[simp] lemma nil_isClosedWalk_iff : G.IsClosedWalk (nil x) ↔ x ∈ G.V := by
  simp [isClosedWalk_iff]

@[simp] lemma nil_isTour_iff : G.IsTour (nil x) ↔ x ∈ G.V := by
  simp [isTour_iff]

@[simp] lemma nil_not_isCycle : ¬ G.IsCycle (nil x) := by
  simp [isCycle_iff]

@[simp]
lemma cons_isClosedWalk : G.IsClosedWalk (cons x e w) ↔ G.IsWalk w ∧ G.Inc₂ e x w.first ∧ x = w.last := by
  simp only [isClosedWalk_iff, cons_isWalk_iff, first_cons, last_cons]
  tauto

@[simp]
lemma cons_isTour : G.IsTour (cons x e w) ↔ G.IsTrail w ∧ G.Inc₂ e x w.first ∧ x = w.last ∧ e ∉ w.edge := by
  simp only [isTour_iff, cons_isClosedWalk, cons_edge, nodup_cons, isTrail_iff]
  tauto

-- @[simp]
-- lemma cons_isCycle : G.IsCycle (cons x e w) ↔ G.IsPath w ∧ G.Inc₂ e x w.first ∧ x = w.last := by
--   simp [isCycle_iff, cons_isClosedWalk, cons_vx, List.tail_cons, isPath_iff]
--   tauto

/-- A subgraph inherits all valid closed walks -/
lemma IsClosedWalk.of_le (h : G.IsClosedWalk w) (hle : G ≤ H) : H.IsClosedWalk w where
  isWalk := h.isWalk.le hle
  first_last := h.first_last

lemma IsClosedWalk.induce (hVd : G.IsClosedWalk w) (hU : w.vxSet ⊆ U) : (G[U]).IsClosedWalk w where
  isWalk := hVd.isWalk.induce hU
  first_last := hVd.first_last

lemma IsClosedWalk.of_vxDel (hVd : (G - U).IsClosedWalk w) : G.IsClosedWalk w := hVd.of_le (vxDel_le G)

lemma IsClosedWalk.vxDel (hVd : G.IsClosedWalk w) (hU : Disjoint w.vxSet U) : (G - U).IsClosedWalk w :=
  hVd.induce <| subset_diff.mpr ⟨hVd.isWalk.vxSet_subset, hU⟩

lemma IsClosedWalk.restrict (hVd : G.IsClosedWalk w) (hF : w.edgeSet ⊆ F) : (G{F}).IsClosedWalk w where
  isWalk := hVd.isWalk.restrict hF
  first_last := hVd.first_last

lemma IsClosedWalk.edgeDel (hVd : G.IsClosedWalk w) (hF : Disjoint w.edgeSet F) : (G \ F).IsClosedWalk w where
  isWalk := hVd.isWalk.edgeDel hF
  first_last := hVd.first_last

lemma IsClosedWalk.of_edgeDel (h : (G \ F).IsClosedWalk w) : G.IsClosedWalk w := h.of_le (edgeDel_le G F)

@[simp]
lemma IsClosedWalk_vxDel : (G - U).IsClosedWalk w ↔ G.IsClosedWalk w ∧ Disjoint w.vxSet U :=
⟨fun h ↦ ⟨h.of_le (vxDel_le G), fun _V hVw hVU _x hxV ↦ (h.isWalk.vxSet_subset <| hVw hxV).2 <| hVU hxV⟩,
  fun ⟨hVd, hU⟩ ↦ hVd.induce (subset_diff.mpr ⟨hVd.isWalk.vxSet_subset, hU⟩)⟩

@[simp]
lemma IsClosedWalk_restrict : (G{F}).IsClosedWalk w ↔ G.IsClosedWalk w ∧ w.edgeSet ⊆ F := by
  refine ⟨fun h ↦ ⟨h.of_le (restrict_le G F), fun e he ↦ ?_⟩, fun ⟨hVd, hF⟩ ↦ hVd.restrict hF⟩
  have := h.isWalk.edgeSet_subset he
  simp only [restrict_E, Set.mem_inter_iff] at this
  exact this.2

@[simp]
lemma IsClosedWalk_edgeDel : (G \ F).IsClosedWalk w ↔ G.IsClosedWalk w ∧ Disjoint w.edgeSet F := by
  rw [edgeDel, IsClosedWalk_restrict, and_congr_right_iff]
  rintro hVd
  simp only [subset_diff, hVd.isWalk.edgeSet_subset, true_and]

/-- A subgraph inherits all valid Tours -/
lemma IsTour.of_le (h : G.IsTour w) (hle : G ≤ H) : H.IsTour w where
  toIsClosedWalk := h.toIsClosedWalk.of_le hle
  edge_nodup := h.edge_nodup

lemma IsTour.induce (h : G.IsTour w) (hU : w.vxSet ⊆ U) : (G[U]).IsTour w where
  toIsClosedWalk := h.toIsClosedWalk.induce hU
  edge_nodup := h.edge_nodup

lemma IsTour.of_vxDel (h : (G - U).IsTour w) : G.IsTour w := h.of_le (vxDel_le G)

lemma IsTour.vxDel (h : G.IsTour w) (hU : Disjoint w.vxSet U) : (G - U).IsTour w :=
  h.induce <| subset_diff.mpr ⟨h.toIsClosedWalk.isWalk.vxSet_subset, hU⟩

lemma IsTour.restrict (h : G.IsTour w) (hF : w.edgeSet ⊆ F) : (G{F}).IsTour w where
  toIsClosedWalk := h.toIsClosedWalk.restrict hF
  edge_nodup := h.edge_nodup

lemma IsTour.edgeDel (h : G.IsTour w) (hF : Disjoint w.edgeSet F) : (G \ F).IsTour w where
  toIsClosedWalk := h.toIsClosedWalk.edgeDel hF
  edge_nodup := h.edge_nodup

lemma IsTour.of_edgeDel (h : (G \ F).IsTour w) : G.IsTour w := h.of_le (edgeDel_le G F)

@[simp]
lemma IsTour_vxDel : (G - U).IsTour w ↔ G.IsTour w ∧ Disjoint w.vxSet U :=
⟨fun h ↦ ⟨h.of_le (vxDel_le G), fun _V hVw hVU _x hxV ↦ (h.toIsClosedWalk.isWalk.vxSet_subset <| hVw hxV).2 <| hVU hxV⟩,
  fun ⟨hVd, hU⟩ ↦ hVd.induce (subset_diff.mpr ⟨hVd.toIsClosedWalk.isWalk.vxSet_subset, hU⟩)⟩

@[simp]
lemma IsTour_restrict : (G{F}).IsTour w ↔ G.IsTour w ∧ w.edgeSet ⊆ F := by
  refine ⟨fun h ↦ ⟨h.of_le (restrict_le G F), fun e he ↦ ?_⟩, fun ⟨hVd, hF⟩ ↦ hVd.restrict hF⟩
  have := h.isWalk.edgeSet_subset he
  simp only [restrict_E, Set.mem_inter_iff] at this
  exact this.2

@[simp]
lemma IsTour_edgeDel : (G \ F).IsTour w ↔ G.IsTour w ∧ Disjoint w.edgeSet F := by
  rw [edgeDel, IsTour_restrict, and_congr_right_iff]
  rintro hVd
  simp only [subset_diff, hVd.toIsClosedWalk.isWalk.edgeSet_subset, true_and]

/-- A subgraph inherits all valid cycles -/
lemma IsCycle.of_le (h : G.IsCycle w) (hle : G ≤ H) : H.IsCycle w where
  toIsTour := h.toIsTour.of_le hle
  nonempty := h.nonempty
  nodup := h.nodup

lemma IsCycle.induce (h : G.IsCycle w) (hU : w.vxSet ⊆ U) : (G[U]).IsCycle w where
  toIsTour := h.toIsTour.induce hU
  nonempty := h.nonempty
  nodup := h.nodup

lemma IsCycle.of_vxDel (h : (G - U).IsCycle w) : G.IsCycle w := h.of_le (vxDel_le G)

lemma IsCycle.vxDel (h : G.IsCycle w) (hU : Disjoint w.vxSet U) : (G - U).IsCycle w :=
  h.induce <| subset_diff.mpr ⟨h.toIsTour.isWalk.vxSet_subset, hU⟩

lemma IsCycle.restrict (h : G.IsCycle w) (hF : w.edgeSet ⊆ F) : (G{F}).IsCycle w where
  toIsTour := h.toIsTour.restrict hF
  nonempty := h.nonempty
  nodup := h.nodup

lemma IsCycle.edgeDel (h : G.IsCycle w) (hF : Disjoint w.edgeSet F) : (G \ F).IsCycle w where
  toIsTour := h.toIsTour.edgeDel hF
  nonempty := h.nonempty
  nodup := h.nodup

lemma IsCycle.of_edgeDel (h : (G \ F).IsCycle w) : G.IsCycle w := h.of_le (edgeDel_le G F)

@[simp]
lemma IsCycle_vxDel : (G - U).IsCycle w ↔ G.IsCycle w ∧ Disjoint w.vxSet U :=
⟨fun h ↦ ⟨h.of_le (vxDel_le G), fun _V hVw hVU _x hxV ↦ (h.toIsTour.isWalk.vxSet_subset <| hVw hxV).2 <| hVU hxV⟩,
  fun ⟨hVd, hU⟩ ↦ hVd.induce (subset_diff.mpr ⟨hVd.isWalk.vxSet_subset, hU⟩)⟩

@[simp]
lemma IsCycle_restrict : (G{F}).IsCycle w ↔ G.IsCycle w ∧ w.edgeSet ⊆ F := by
  refine ⟨fun h ↦ ⟨h.of_le (restrict_le G F), fun e he ↦ ?_⟩, fun ⟨hVd, hF⟩ ↦ hVd.restrict hF⟩
  have := h.isWalk.edgeSet_subset he
  simp only [restrict_E, Set.mem_inter_iff] at this
  exact this.2

@[simp]
lemma IsCycle_edgeDel : (G \ F).IsCycle w ↔ G.IsCycle w ∧ Disjoint w.edgeSet F := by
  rw [edgeDel, IsCycle_restrict, and_congr_right_iff]
  rintro hVd
  simp only [subset_diff, hVd.toIsTour.isWalk.edgeSet_subset, true_and]

/-- The requirement for a cycle to be a tour is really to prevent a backtrack to be a cycle.
If a walk is longer than 2, this requirement can be dropped. -/
lemma IsWalk.isCycle_of_length (hVd : G.IsWalk w) (hfirst : w.first = w.last) (hlen : 2 < w.length)
    (hvx : w.vx.tail.Nodup) : G.IsCycle w where
  isWalk := hVd
  first_last := hfirst
  edge_nodup := by
    cases w with
    | nil => simp_all
    | cons u e w =>
      obtain ⟨hbtw, hVd⟩ := cons_isWalk_iff.mp hVd
      simp_all only [ne_eq, forall_const, cons_isWalk_iff, and_self, first_cons, last_cons,
        cons_length, cons_vx, List.tail_cons, cons_edge, nodup_cons, Nat.reduceEqDiff]
      subst u
      have hP : G.IsPath w := ⟨hVd, hvx⟩
      refine ⟨?_, hP.isTrail.edge_nodup⟩
      contrapose! hlen
      obtain ⟨w', heq, hw'P, hlink⟩ := hP.exists_cons hlen hbtw.symm
      obtain ⟨x, rfl⟩ := nil_iff_eq_nil.mp <| hw'P.first_eq_last.mp <|
        hlink.trans (by rw [heq, last_cons])
      rw [heq]
      simp
  nonempty := by_contra fun h ↦ by
    rw [w.not_nonempty_iff, ← w.length_eq_zero] at h
    omega
  nodup := hvx

lemma Inc₂.walk_isCycle (h : G.Inc₂ e u u) : G.IsCycle h.walk where
  isWalk := h.walk_isWalk
  first_last := by simp
  edge_nodup := by simp
  nonempty := by simp
  nodup := by simp

lemma IsCycle.tail_isPath (h : G.IsCycle w) : G.IsPath w.tail where
  isWalk := h.isWalk.suffix <| tail_isSuffix w
  nodup := tail_vx_nodup_iff.mpr h.nodup

namespace Inc₂

/-- The walk corresponding to an incidence `G.Inc₂ e u v` and then backtracking to `u` using the
same edge. -/
def backtrack (_h : G.Inc₂ e u v) : WList α β := cons u e (cons v e (nil u))

@[simp]
lemma backtrack_first (h : G.Inc₂ e u v) : h.backtrack.first = u := rfl

@[simp]
lemma backtrack_last (h : G.Inc₂ e u v) : h.backtrack.last = u := by
  simp [backtrack]

@[simp]
lemma backtrack_nonempty (h : G.Inc₂ e u v) : h.backtrack.Nonempty := by simp [backtrack]

@[simp]
lemma backtrack_vx (h : G.Inc₂ e u v) : h.backtrack.vx = [u, v, u] := by simp [backtrack]

@[simp]
lemma mem_backtrack_iff (h : G.Inc₂ e u v) (x : α) : x ∈ h.backtrack ↔ x = u ∨ x = v := by
  simp only [backtrack, mem_cons_iff, WList.mem_nil_iff]
  tauto

@[simp]
lemma backtrack_vxSet (h : G.Inc₂ e u v) : h.backtrack.vxSet = {u, v} := by
  simp [backtrack, Set.pair_comm]

@[simp]
lemma backtrack_edge (h : G.Inc₂ e u v) : h.backtrack.edge = [e, e] := by simp [backtrack]

@[simp]
lemma backtrack_edgeSet (h : G.Inc₂ e u v) : h.backtrack.edgeSet = {e} := by
  simp [backtrack, Set.pair_comm]

@[simp]
lemma backtrack_length (h : G.Inc₂ e u v) : h.backtrack.length = 2 := by simp [backtrack]

@[simp]
lemma backtrack_isWalk (h : G.Inc₂ e u v) : G.IsWalk h.backtrack := by
  simp [backtrack, h, h.symm, h.vx_mem_left]

end Inc₂

-- lemma IsTour.exists_cycle_sublist {w : WList α β} (h : G.IsTour w) :
--     w.Nil ∨ (∃ c : WList α β, G.IsCycle c ∧ c.IsSublist w) :=
--   match hlen : w.length with
--   | 0 => Or.inl (length_eq_zero.mp hlen)
--   | n + 1 => by
--     classical
--     right
--     by_cases hex : ∀ x, w.vx.tail.count x ≤ 1
--     · refine ⟨w, ⟨h, ?_, by simpa [← List.nodup_iff_count_le_one] using hex⟩, isSublist_refl _⟩
--       rw [← WList.length_pos_iff]
--       linarith
--     obtain ⟨x, hcount⟩ := by simpa using hex
--     let w' := w.suffixFromVx x |>.prefixUntilLast (· = x) ; clear hex hlen n
--     have hNonempty : w'.Nonempty := by
--       simp_rw [w', prefixUntilLast, reverse_nonempty, suffixFrom_nonempty_iff, reverse_vx,
--         dropLast_reverse, List.mem_reverse, ← count_pos_iff]
--       use x, ?_
--       have : 1 < w.vx.count x := Nat.lt_of_lt_of_le hcount (w.vx.count_tail_le x)
--       rw [← suffixFromVx_vx_count] at this
--       have := (w.suffixFromVx x).vx.le_count_tail x
--       omega
--     have hw'Sublist : w'.IsSublist w := prefixUntilLast_isPrefix _ _ |>.isSublist |>.trans
--       <| suffixFromVx_isSuffix w x |>.isSublist
--     have hw'len : w'.length < w.length := by
--       refine Nat.lt_of_le_of_ne hw'Sublist.length_le fun hlen ↦ ?_
--       obtain heq : w' = w := hw'Sublist.eq_of_length_ge hlen.ge ; clear hlen hw'Sublist

--       sorry
--     have hw' : G.IsTour w' := sorry
--     obtain ⟨c, hcyc, hcSubw'⟩ := hw'.exists_cycle_sublist.resolve_left hNonempty.not_nil
--     exact ⟨c, hcyc, hcSubw'.trans hw'Sublist⟩
-- termination_by w.length



-- lemma IsClosedWalk.backtrack_sublist_or_cycle_sublist (h : G.IsClosedWalk w) :
--     w.Nil ∨ (∃ h : G.Inc₂ e u v, h.backtrack.IsSublist w) ∨
--     (∃ c : WList α β, G.IsCycle c ∧ c.IsSublist w) := by
--   match h : w.length with
--   | 0 =>
--     left
--     exact WList.length_eq_zero.mp h
--   | n + 1 =>
--     right
