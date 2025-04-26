import Kura.Walk.Basic

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

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
  {w w₁ w₂ : WList α β} {S T : Set α}

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
  simp only [isClosedWalk_iff, cons_isWalk_iff, cons_first, cons_last]
  tauto

@[simp]
lemma cons_isTour : G.IsTour (cons x e w) ↔ G.IsTrail w ∧ G.Inc₂ e x w.first ∧ x = w.last ∧ e ∉ w.edge := by
  simp only [isTour_iff, cons_isClosedWalk, cons_edge, nodup_cons, isTrail_iff]
  tauto

-- @[simp]
-- lemma cons_isCycle : G.IsCycle (cons x e w) ↔ G.IsPath w ∧ G.Inc₂ e x w.first ∧ x = w.last := by
--   simp [isCycle_iff, cons_isClosedWalk, cons_vx, List.tail_cons, isPath_iff]
--   tauto

lemma IsWalk.isCycle' (hVd : G.IsWalk w) (hfirst : w.first = w.last) (hlen : 2 < w.length)
    (hvx : w.vx.tail.Nodup) : G.IsCycle w where
  isWalk := hVd
  first_last := hfirst
  edge_nodup := by
    cases w with
    | nil => simp_all
    | cons u e w =>
      obtain ⟨hbtw, hVd⟩ := cons_isWalk_iff.mp hVd
      simp_all only [ne_eq, forall_const, cons_isWalk_iff, and_self, cons_first, cons_last,
        cons_length, cons_vx, List.tail_cons, cons_edge, nodup_cons, Nat.reduceEqDiff]
      subst u
      have hP : G.IsPath w := ⟨hVd, hvx⟩
      refine ⟨?_, hP.isTrail.edge_nodup⟩
      contrapose! hlen
      obtain ⟨w', heq, hw'P, hlink⟩ := hP.exists_cons hlen hbtw.symm
      obtain ⟨x, rfl⟩ := nil_iff_eq_nil.mp <| hw'P.first_eq_last.mp <|
        hlink.trans (by rw [heq, cons_last])
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
