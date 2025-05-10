/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
import Mathlib.Data.Sym.Sym2
import Mathlib.Topology.Instances.ENat
import Kura.Dep.Finset

/-!
# Multigraphs

A multigraph is a set of vertices and a set of edges,
together with incidence data that associates each edge `e`
with an unordered pair `(x,y)` of vertices.
`x` and `y` may be equal, in which case `e` is a 'loop',
and there may also be more than one edge `e` associated with each pair `x` and `y`.
A multigraph where neither of these occurs is 'simple',
and these objects are described by `SimpleGraph`.

This module defines `Graph α β` for a vertex type `α` and an edge type `β`,
and gives basic API for incidence and adjacency.

## Main definitions

For `G : Graph α β`, ...

* `G.V` denotes the vertex set of `G` as a term in `Set α`.
* `G.E` denotes the edge set of `G` as a term in `Set β`.
* `G.Inc₂ e x y` means that the edge `e : β` has vertices `x : α` and `y : α` as its ends.
* `G.Inc e x` means that the edge `e : β` has `x` as one of its ends.
* `G.Adj x y` means that there is an edge `e` having `x` and `y` as its ends.
* `G.IsLoopAt e x` means that `e` is a loop edge with both ends equal to `x`.
* `G.IsNonloopAt e x` means that `e` is a non-loop edge with one end equal to `x`.

## Implementation notes

Unlike the design of `SimpleGraph`, the vertex and edge sets of `G` are modelled as sets
`G.V : Set α` and `G.E : Set β`, within ambient types, rather than being types themselves.
This mimics the 'embedded set' design used in `Matroid`, which seems to be more amenable to
formalizing real-world proofs in combinatorics.

A specific advantage is that this will allow subgraphs of `G : Graph α β` to also be terms in
`Graph α β`, and so there is no need for an extensive `Graph.subgraph` API and all the associated
definitions and canonical coercion maps. The same will go for minors and the various other
partial orders on multigraphs.

The main tradeoff is that certain parts of the API will require caring about whether a term
`x : α` or `e : β` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely quite amenable to automation.

## Notation

Relecting written mathematics, we use the compact notations `G.V` and `G.E` to describe
vertex and edge sets formally, but use the longer terms `vxSet` and `edgeSet` within
lemma names to refer to the same objects.

-/

variable {α β : Type*} {x y z u v w : α} {e f : β}

open Set

/-- A multigraph with vertex set `V : Set α` and edge set `E : Set β`,
as described by a predicate describing whether an edge `e : β` has ends `x` and `y`. -/
structure Graph (α β : Type*) where
  /-- The vertex set. -/
  V : Set α
  /-- The edge set. -/
  E : Set β
  /-- The predicate that an edge `e` goes from `x` to `y`. -/
  Inc₂ : β → α → α → Prop
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  inc₂_symm : ∀ ⦃e x y⦄, Inc₂ e x y → Inc₂ e y x
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_inc₂_of_inc₂ : ∀ ⦃e x y v w⦄, Inc₂ e x y → Inc₂ e v w → x = v ∨ x = w
  /-- If `e` is incident to something, then `e` is in the edge set -/
  edge_mem_iff_exists_inc₂ : ∀ e, e ∈ E ↔ ∃ x y, Inc₂ e x y
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  vx_mem_left_of_inc₂ : ∀ ⦃e x y⦄, Inc₂ e x y → x ∈ V

initialize_simps_projections Graph (V → vxSet, E → edgeSet, Inc₂ → inc₂)

namespace Graph

variable {G H : Graph α β}

/-! ### Edge-vertex-vertex incidence -/

lemma Inc₂.symm (h : G.Inc₂ e x y) : G.Inc₂ e y x :=
  G.inc₂_symm h

lemma inc₂_comm : G.Inc₂ e x y ↔ G.Inc₂ e y x :=
  ⟨Inc₂.symm, Inc₂.symm⟩

lemma Inc₂.edge_mem (h : G.Inc₂ e x y) : e ∈ G.E :=
  (edge_mem_iff_exists_inc₂ ..).2 ⟨x, y, h⟩

lemma Inc₂.vx_mem_left (h : G.Inc₂ e x y) : x ∈ G.V :=
  G.vx_mem_left_of_inc₂ h

lemma Inc₂.vx_mem_right (h : G.Inc₂ e x y) : y ∈ G.V :=
  h.symm.vx_mem_left

lemma exists_inc₂_of_mem_edgeSet (h : e ∈ G.E) : ∃ x y, G.Inc₂ e x y :=
  (edge_mem_iff_exists_inc₂ ..).1 h

lemma Inc₂.left_eq_or_eq_of_inc₂ (h : G.Inc₂ e x y) (h' : G.Inc₂ e z w) : x = z ∨ x = w :=
  G.eq_or_eq_of_inc₂_of_inc₂ h h'

lemma Inc₂.left_eq_of_inc₂_of_ne (h : G.Inc₂ e x y) (h' : G.Inc₂ e z w) (hzx : x ≠ z) : x = w :=
  (h.left_eq_or_eq_of_inc₂ h').elim (False.elim ∘ hzx) id

lemma Inc₂.eq_of_inc₂ (h : G.Inc₂ e x y) (h' : G.Inc₂ e x z) : y = z := by
  obtain rfl | rfl := h.symm.left_eq_or_eq_of_inc₂ h'.symm; rfl
  obtain rfl | rfl := h'.symm.left_eq_or_eq_of_inc₂ h.symm <;> rfl

lemma Inc₂.inc₂_iff_eq (h : G.Inc₂ e x y) : G.Inc₂ e x z ↔ z = y :=
  ⟨fun h' ↦ h'.eq_of_inc₂ h, fun h' ↦ h' ▸ h⟩

lemma edgeSet_eq_setOf_exists_inc₂ : G.E = {e | ∃ x y, G.Inc₂ e x y} :=
  Set.ext fun e ↦ G.edge_mem_iff_exists_inc₂ e

@[simp]
lemma not_inc₂_of_not_mem_edgeSet (he : e ∉ G.E) (x y : α) : ¬ G.Inc₂ e x y := by
  contrapose! he
  exact he.edge_mem

@[simp]
lemma not_inc₂_of_left_not_mem_vxSet (x : α) (hx : x ∉ G.V) : ¬ G.Inc₂ e x y := by
  contrapose! hx
  exact hx.vx_mem_left

@[simp]
lemma not_inc₂_of_right_not_mem_vxSet (y : α) (hy : y ∉ G.V) : ¬ G.Inc₂ e x y := by
  contrapose! hy
  exact hy.vx_mem_right

lemma Inc₂.inc₂_iff_eq_left {x' : α} (h : G.Inc₂ e x y) : G.Inc₂ e x' y ↔ x = x' := by
  constructor
  · rintro h'
    obtain rfl | rfl := h.left_eq_or_eq_of_inc₂ h'
    · rfl
    obtain rfl | rfl := h'.left_eq_or_eq_of_inc₂ h <;> rfl
  · rintro rfl
    exact h

lemma Inc₂.inc₂_iff_eq_right {y' : α} (h : G.Inc₂ e x y) : G.Inc₂ e x y' ↔ y = y' := by
  rw [inc₂_comm, h.symm.inc₂_iff_eq_left]

lemma Inc₂.eq_and_eq_or_eq_and_eq_of_inc₂ {x' y' : α} (h : G.Inc₂ e x y) (h' : G.Inc₂ e x' y') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  obtain rfl | rfl := h.left_eq_or_eq_of_inc₂ h'
  on_goal 1 => obtain rfl := h.inc₂_iff_eq_right.mp h'
  on_goal 2 => obtain rfl := h.symm.inc₂_iff_eq_left.mp h'
  all_goals tauto

lemma Inc₂.inc₂_iff (h : G.Inc₂ e x y) {x' y' : α} :
    G.Inc₂ e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  refine ⟨h.eq_and_eq_or_eq_and_eq_of_inc₂, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl,rfl⟩)
  · assumption
  exact h.symm

lemma Inc₂.inc₂_iff_sym2_eq (h : G.Inc₂ e x y) {x' y' : α} :
    G.Inc₂ e x' y' ↔ s(x,y) = s(x',y') := by
  rw [h.inc₂_iff, Sym2.eq_iff]

/-! ### Edge-vertex incidence -/

/-- `G.Inc e x` means that `x` is one of the ends of `e`. -/
def Inc (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, G.Inc₂ e x y

lemma inc_iff_exists_inc₂ : G.Inc e x ↔ ∃ y, G.Inc₂ e x y := Iff.rfl
alias ⟨Inc.exists_vx_inc₂, _⟩ := inc_iff_exists_inc₂

@[simp]
lemma Inc.edge_mem (h : G.Inc e x) : e ∈ G.E :=
  h.choose_spec.edge_mem

@[simp]
lemma Inc.vx_mem (h : G.Inc e x) : x ∈ G.V :=
  h.choose_spec.vx_mem_left

@[simp]
lemma Inc₂.inc_left (h : G.Inc₂ e x y) : G.Inc e x :=
  ⟨y, h⟩

@[simp]
lemma Inc₂.inc_right (h : G.Inc₂ e x y) : G.Inc e y :=
  ⟨x, h.symm⟩

lemma Inc.eq_or_eq_of_inc₂ (h : G.Inc e x) (h' : G.Inc₂ e y z) : x = y ∨ x = z :=
  h.choose_spec.left_eq_or_eq_of_inc₂ h'

lemma Inc₂.eq_or_eq_of_inc (h : G.Inc₂ e x y) (h' : G.Inc e z) : x = z ∨ y = z := by
  have := h'.eq_or_eq_of_inc₂ h
  tauto

lemma Inc.eq_of_inc₂_of_ne_left (h : G.Inc e x) (h' : G.Inc₂ e y z) (hxy : x ≠ y) : x = z :=
  (h.eq_or_eq_of_inc₂ h').elim (False.elim ∘ hxy) id

@[simp]
lemma not_inc_of_not_mem_edgeSet (he : e ∉ G.E) (x : α) : ¬ G.Inc e x :=
  (he ·.edge_mem)

@[simp]
lemma not_inc_of_not_mem_vxSet (x : α) (hx : x ∉ G.V) : ¬ G.Inc e x := by
  contrapose! hx
  exact hx.vx_mem

lemma exists_inc_of_mem_edgeSet (he : e ∈ G.E) : ∃ x, G.Inc e x := by
  obtain ⟨y, z, h⟩ := exists_inc₂_of_mem_edgeSet he
  exact ⟨y, h.inc_left⟩

/-- Given a proof that `e` is incident with `x`, noncomputably find the other end of `e`.
(If `e` is a loop, this is equal to `x` itself). -/
noncomputable def Inc.other (h : G.Inc e x) : α := h.choose

@[simp]
lemma Inc.inc₂_other (h : G.Inc e x) : G.Inc₂ e x h.other :=
  h.choose_spec

@[simp]
lemma Inc.inc_other (h : G.Inc e x) : G.Inc e h.other :=
  h.inc₂_other.inc_right

lemma Inc.eq_or_eq_or_eq_of_inc_of_inc (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  by_contra! hcon
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_inc₂_of_ne_left hx' hcon.1.symm
  obtain rfl := hz.eq_of_inc₂_of_ne_left hx' hcon.2.1.symm
  exact hcon.2.2 rfl

/-- The binary incidence predicate can be expressed in terms of the unary one. -/
lemma inc₂_iff_inc : G.Inc₂ e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.eq_or_eq_of_inc₂ h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq_of_inc₂ hy'
    · assumption
    exact hy'.symm
  assumption

lemma Inc.inc₂_of_inc_of_ne (h : G.Inc e x) (h' : G.Inc e y) (hxy : x ≠ y) : G.Inc₂ e x y := by
  obtain ⟨z, hz⟩ := h
  obtain rfl | rfl := hz.eq_or_eq_of_inc h'
  · simp at hxy
  exact hz

/-- `G.IsLoopAt e x` means that `e` is a loop edge at the vertex `x`. -/
def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.Inc₂ e x x

lemma inc₂_self_iff : G.Inc₂ e x x ↔ G.IsLoopAt e x := Iff.rfl

lemma IsLoopAt.inc₂ (h : G.IsLoopAt e x) : G.Inc₂ e x x := h

lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x :=
  Inc₂.inc_left h

lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  obtain rfl | rfl := h'.eq_or_eq_of_inc₂ h <;> rfl

lemma IsLoopAt.inc₂_iff_eq (h : G.IsLoopAt e x) : G.Inc₂ e x y ↔ x = y :=
  ⟨h.eq_of_inc₂, fun h' ↦ by rwa [← h']⟩

@[simp]
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ G.E :=
  h.inc.edge_mem

@[simp]
lemma IsLoopAt.vx_mem (h : G.IsLoopAt e x) : x ∈ G.V :=
  h.inc.vx_mem

/-- `G.IsNonloopAt e x` means that `e` is an edge from `x` to some `y ≠ x`. -/
@[mk_iff]
structure IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop where
  inc : G.Inc e x
  exists_inc₂_ne : ∃ y ≠ x, G.Inc₂ e x y

@[simp]
lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ G.E :=
  h.inc.edge_mem

@[simp]
lemma IsNonloopAt.vx_mem (h : G.IsNonloopAt e x) : x ∈ G.V :=
  h.inc.vx_mem

lemma IsLoopAt.not_isNonloop_at (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  intro h'
  obtain ⟨z, hyz, hy⟩ := h'.exists_inc₂_ne
  rw [← h.eq_of_inc hy.inc_left, ← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl

lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y :=
  fun h' ↦ h'.not_isNonloop_at x h

lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  obtain ⟨y, hy⟩ := h
  obtain rfl | hne := eq_or_ne x y
  · exact .inl hy
  exact .inr ⟨hy.inc_left, y, hne.symm, hy⟩

lemma Inc.isLoopAt_or_inc₂_ne (h : G.Inc e x) : G.IsLoopAt e x ∨ ∃ y ≠ x, G.Inc₂ e x y := by
  obtain ⟨y, hy⟩ := h
  obtain rfl | hne := eq_or_ne x y
  · exact .inl hy
  exact .inr ⟨y, hne.symm, hy⟩

lemma Inc₂.isNonloopAt_iff_ne (h : G.Inc₂ e x y) : G.IsNonloopAt e x ↔ x ≠ y := by
  obtain rfl | hne := eq_or_ne x y
  · exact iff_of_false (IsLoopAt.not_isNonloop_at h x) <| by simp
  rw [isNonloopAt_iff]
  exact iff_of_true ⟨h.inc_left, ⟨y, hne.symm, h⟩⟩ hne

lemma Inc₂.isNonloopAt_of_ne (h : G.Inc₂ e x y) (hxy : x ≠ y) : G.IsNonloopAt e x :=
  h.isNonloopAt_iff_ne.2 hxy

lemma Inc₂.isNonloopAt_right_of_ne (h : G.Inc₂ e x y) (hxy : x ≠ y) : G.IsNonloopAt e y :=
  h.symm.isNonloopAt_iff_ne.2 hxy.symm

lemma exists_isLoopAt_or_inc₂_of_mem_edgeSet (h : e ∈ G.E) :
    (∃ x, G.IsLoopAt e x) ∨ ∃ x y, G.Inc₂ e x y ∧ x ≠ y := by
  obtain ⟨x, y, h⟩ := exists_inc₂_of_mem_edgeSet h
  obtain rfl | hne := eq_or_ne x y
  · exact .inl ⟨x, h⟩
  exact .inr ⟨x, y, h, hne⟩

/-! ### Adjacency -/

/-- `G.Adj x y` means that `G` has an edge from `x` to `y`. -/
def Adj (G : Graph α β) (x y : α) : Prop := ∃ e, G.Inc₂ e x y

lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩

lemma adj_comm : G.Adj x y ↔ G.Adj y x :=
  ⟨Adj.symm, Adj.symm⟩

@[simp]
lemma Adj.mem_left (h : G.Adj x y) : x ∈ G.V :=
  h.choose_spec.vx_mem_left

@[simp]
lemma Adj.mem_right (h : G.Adj x y) : y ∈ G.V :=
  h.symm.mem_left

lemma Inc₂.adj (h : G.Inc₂ e x y) : G.Adj x y :=
  ⟨e, h⟩

lemma not_adj_of_left_not_mem_vxSet (x : α) (hx : x ∉ G.V) : ¬ G.Adj x y := by
  contrapose! hx
  exact hx.mem_left

lemma not_adj_of_right_not_mem_vxSet (y : α) (hy : y ∉ G.V) : ¬ G.Adj x y := by
  contrapose! hy
  exact hy.mem_right

/-! ### Multiset/Sym2 incidence functions -/

section toMultiset

noncomputable def toMultiset (G : Graph α β) (e : β) : Multiset α := by
  classical
  exact if he : e ∈ G.E
    then {G.exists_inc₂_of_mem_edgeSet he |>.choose,
          G.exists_inc₂_of_mem_edgeSet he |>.choose_spec.choose}
    else 0

@[simp]
lemma vx_mem_of_mem_toMultiset (hxe : x ∈ G.toMultiset e) : x ∈ G.V := by
  simp only [toMultiset] at hxe
  split_ifs at hxe with he
  · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hxe
    obtain rfl | rfl := hxe
    · exact (G.exists_inc₂_of_mem_edgeSet he).choose_spec.choose_spec.vx_mem_left
    · exact (G.exists_inc₂_of_mem_edgeSet he).choose_spec.choose_spec.vx_mem_right
  · exact (Multiset.not_mem_zero _ hxe).elim

@[simp]
lemma edge_mem_of_mem_toMultiset (hxe : x ∈ G.toMultiset e) : e ∈ G.E := by
  simp only [toMultiset] at hxe
  split_ifs at hxe with he
  · exact (G.exists_inc₂_of_mem_edgeSet he).choose_spec.choose_spec.edge_mem
  · exact (Multiset.not_mem_zero _ hxe).elim

@[simp]
lemma toMultiset_card_eq_two (he : e ∈ G.E) : (G.toMultiset e).card = 2 := by
  simp only [toMultiset, he, ↓reduceDIte, Multiset.insert_eq_cons, Multiset.card_cons,
    Multiset.card_singleton, Nat.reduceAdd]

@[simp]
lemma toMultiset_eq_zero (he : e ∉ G.E) : G.toMultiset e = 0 := by
  simp only [toMultiset, he, ↓reduceDIte]

@[simp]
lemma toMultiset_eq_zero_iff : G.toMultiset e = 0 ↔ e ∉ G.E := by
  refine ⟨fun h he ↦ ?_, toMultiset_eq_zero⟩
  have := h ▸ toMultiset_card_eq_two he
  simp at this

@[simp]
lemma toMultiset_card_eq_two_iff : (G.toMultiset e).card = 2 ↔ e ∈ G.E := by
  refine ⟨fun h ↦ ?_, fun he ↦ ?_⟩
  · rw [Multiset.card_eq_two] at h
    obtain ⟨x, y, hxy⟩ := h
    exact edge_mem_of_mem_toMultiset (by rw [hxy]; simp : x ∈ G.toMultiset e)
  · rw [toMultiset_card_eq_two he]

lemma toMultiset_card_or : (G.toMultiset e).card = 2 ∨ (G.toMultiset e).card = 0 := by
  by_cases he : e ∈ G.E
  · exact Or.inl (toMultiset_card_eq_two_iff.mpr he)
  · exact Or.inr (Multiset.card_eq_zero.mpr (toMultiset_eq_zero_iff.mpr he))

@[simp]
lemma toMultiset_eq_pair_iff : G.toMultiset e = {x, y} ↔ G.Inc₂ e x y := by
  constructor <;> rintro h
  · have he := edge_mem_of_mem_toMultiset (by rw [h]; simp : x ∈ G.toMultiset e)
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := by simpa only [toMultiset, he, ↓reduceDIte, Multiset.pair_eq_pair_iff] using h
    · exact (G.exists_inc₂_of_mem_edgeSet he).choose_spec.choose_spec
    · exact (G.exists_inc₂_of_mem_edgeSet he).choose_spec.choose_spec.symm
  · simp only [Graph.toMultiset, h.edge_mem, ↓reduceDIte]
    let huv := (G.exists_inc₂_of_mem_edgeSet h.edge_mem).choose_spec.choose_spec
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := huv.eq_and_eq_or_eq_and_eq_of_inc₂ h <;> simp_rw [← h1, ← h2]
    rw [Multiset.pair_comm]

alias ⟨_, Inc₂.toMultiset⟩ := toMultiset_eq_pair_iff

@[simp]
lemma inc_iff_mem_toMultiset : x ∈ G.toMultiset e ↔ G.Inc e x := by
  constructor
  · rintro h
    obtain ⟨u, v, huv⟩ := G.exists_inc₂_of_mem_edgeSet (edge_mem_of_mem_toMultiset h)
    simp only [huv.toMultiset, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h
    obtain rfl | rfl := h
    · exact huv.inc_left
    · exact huv.inc_right
  · rintro ⟨y, h⟩
    simp [h.toMultiset]

alias ⟨_, Inc.mem_toMultiset⟩ := inc_iff_mem_toMultiset

end toMultiset

section toSym2

noncomputable def toSym2 (G : Graph α β) (e : β) (he : e ∈ G.E) : Sym2 α :=
  s(G.exists_inc₂_of_mem_edgeSet he |>.choose, G.exists_inc₂_of_mem_edgeSet he |>.choose_spec.choose)

@[simp]
lemma vx_mem_of_toSym2 {he : e ∈ G.E} (h : x ∈ G.toSym2 e he) : x ∈ G.V := by
  have := (G.exists_inc₂_of_mem_edgeSet he).choose_spec.choose_spec
  obtain rfl | rfl := by simpa [toSym2] using h
  · exact this.vx_mem_left
  · exact this.vx_mem_right

@[simp]
lemma toSym2_eq_pair_iff (he : e ∈ G.E) : G.toSym2 e he = s(x, y) ↔ G.Inc₂ e x y := by
  have := (G.exists_inc₂_of_mem_edgeSet he).choose_spec.choose_spec
  constructor <;> rintro h
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := by simpa [toSym2] using h
    · exact this
    · exact this.symm
  · simpa [toSym2] using this.eq_and_eq_or_eq_and_eq_of_inc₂ h

lemma Inc₂.toSym2 (h : G.Inc₂ e x y) : G.toSym2 e h.edge_mem = s(x, y) := by
  rwa [toSym2_eq_pair_iff h.edge_mem]

noncomputable def func (G : Graph α β) (e : G.E): Sym2 G.V :=
  let H := G.exists_inc₂_of_mem_edgeSet e.prop
  s(⟨H.choose, H.choose_spec.choose_spec.vx_mem_left⟩,
    ⟨H.choose_spec.choose, H.choose_spec.choose_spec.vx_mem_right⟩)

@[simp] lemma func_eq_pair_iff {x y : G.V} {e : G.E} :
    G.func e = s(x, y) ↔ G.Inc₂ e x y := by
  let H := G.exists_inc₂_of_mem_edgeSet e.prop
  let a := H.choose
  let b := H.choose_spec.choose
  let h := H.choose_spec.choose_spec
  simp only [func]
  change s(⟨a, h.vx_mem_left⟩, ⟨b, h.vx_mem_right⟩) = s(x, y) ↔ G.Inc₂ e x y
  constructor <;> rintro hbtw
  · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hbtw
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hbtw
    · exact H.choose_spec.choose_spec
    · exact H.choose_spec.choose_spec.symm
  · simp [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, Subtype.ext_iff]
    exact h.eq_and_eq_or_eq_and_eq_of_inc₂ hbtw

lemma Inc₂.func (h : G.Inc₂ e x y) :
    G.func ⟨e, h.edge_mem⟩ = s(⟨x, h.vx_mem_left⟩, ⟨y, h.vx_mem_right⟩) := by simpa

lemma exists_func_pair (e : G.E) : ∃ x y, G.func e = s(x, y) := by
  let H := G.exists_inc₂_of_mem_edgeSet e.prop
  let a := H.choose
  let b := H.choose_spec.choose
  let h := H.choose_spec.choose_spec
  exact ⟨⟨a, h.vx_mem_left⟩, ⟨b, h.vx_mem_right⟩, H.choose_spec.choose_spec.func⟩

end toSym2

section incFun

noncomputable def incFun (G : Graph α β) (e : β) : α →₀ ℕ := by
  classical
  exact (G.toMultiset e).toFinsupp

lemma Inc₂.incFun_support_eq [DecidableEq α] (h : G.Inc₂ e x y) :
    (G.incFun e).support = {x,y} := by
  simp only [incFun, h.toMultiset, Multiset.insert_eq_cons, Multiset.toFinsupp_support,
    Multiset.toFinset_cons, Multiset.toFinset_singleton]
  convert rfl

-- @[simp] lemma _root_.Set.singleton_inter_eq (x : α) (s : Set α) [Decidable (x ∈ s)] :
--     {x} ∩ s = if x ∈ s then {x} else ∅ := by
--   split_ifs <;> simpa

-- @[simp] lemma _root_.Set.inter_singleton_eq (x : α) (s : Set α) [Decidable (x ∈ s)] :
--     s ∩ {x} = if x ∈ s then {x} else ∅ := by
--   split_ifs <;> simpa

lemma incFun_eq_zero_of_not_mem (he : e ∉ G.E) : G.incFun e = 0 := by
  simp [DFunLike.ext_iff, incFun, inc_iff_exists_inc₂, not_inc₂_of_not_mem_edgeSet he]

lemma incFun_le_two (G : Graph α β) (e : β) (x : α) : G.incFun e x ≤ 2 := by
  classical
  obtain ⟨y, hy⟩ | hx := em <| G.Inc e x
  · rw [incFun, Multiset.toFinsupp_apply, ← toMultiset_card_eq_two_iff.mpr (hy.edge_mem)]
    exact Multiset.count_le_card x _
  simp [incFun, inc₂_iff_inc, hx]

lemma IsNonloopAt.IncFun_eq_one (h : G.IsNonloopAt e x) : G.incFun e x = 1 := by
  obtain ⟨y, hne, hxy⟩ := h.exists_inc₂_ne
  rw [← toMultiset_eq_pair_iff] at hxy
  simp [incFun, hxy, hne.symm]

@[simp]
lemma incFun_eq_one_iff : G.incFun e x = 1 ↔ G.IsNonloopAt e x := by
  obtain (⟨y, hxy⟩ | hex) := em <| G.Inc e x
  · simp [hxy.isNonloopAt_iff_ne, incFun, toMultiset_eq_pair_iff.mpr hxy]
  simp [incFun, mt Inc₂.inc_left hex, mt IsNonloopAt.inc hex]
  rw [← inc_iff_mem_toMultiset] at hex
  simp_all

lemma IsNonloopAt.incFun_eq_one (h : G.IsNonloopAt e x) : G.incFun e x = 1 :=
  incFun_eq_one_iff.2 h

@[simp]
lemma incFun_eq_two_iff : G.incFun e x = 2 ↔ G.IsLoopAt e x := by
  obtain (⟨y, hxy⟩ | hex) := em <| G.Inc e x
  · simp only [incFun, toMultiset_eq_pair_iff.mpr hxy, Multiset.insert_eq_cons,
    Multiset.toFinsupp_apply, Multiset.count_cons_self, Multiset.nodup_singleton,
    Multiset.count_singleton, Nat.reduceEqDiff, ite_eq_left_iff, zero_ne_one, imp_false, not_not, ←
    inc₂_self_iff, hxy.inc₂_iff_eq_right]
    exact eq_comm
  simp [incFun, mt Inc₂.inc_left hex, hex, mt IsLoopAt.inc hex]

lemma IsLoopAt.incFun_eq_two (h : G.IsLoopAt e x) : G.incFun e x = 2 :=
  incFun_eq_two_iff.2 h

@[simp]
lemma incFun_eq_zero_iff : G.incFun e = 0 ↔ e ∉ G.E := by
  refine ⟨fun h he ↦ ?_, incFun_eq_zero_of_not_mem⟩
  obtain ⟨x, y, hxy⟩ := exists_inc₂_of_mem_edgeSet he
  obtain hx | hx := hxy.inc_left.isLoopAt_or_isNonloopAt
  · have := h ▸ hx.incFun_eq_two
    simp at this
  have := h ▸ hx.incFun_eq_one
  simp at this

lemma sum_incFun_eq_two (he : e ∈ G.E) : (G.incFun e).sum (fun _ x ↦ x) = 2 := by
  classical
  obtain ⟨x, y, hxy⟩ := exists_inc₂_of_mem_edgeSet he
  obtain rfl | hne := eq_or_ne x y
  · simp [Finsupp.sum, hxy.incFun_support_eq, hxy.inc₂_iff_eq, show G.IsLoopAt e x from hxy]
  simp [Finsupp.sum, hxy.incFun_support_eq, Finset.sum_pair hne,
    (hxy.isNonloopAt_of_ne hne).incFun_eq_one, (hxy.isNonloopAt_right_of_ne hne).incFun_eq_one]

@[simp]
lemma toMultiset_count [DecidableEq α] (x : α) : (G.toMultiset e).count x = G.incFun e x := by
  classical
  by_cases he : e ∈ G.E
  · simp only [toMultiset, he, ↓reduceDIte, incFun]
    convert (Multiset.toFinsupp_apply _ x).symm
  · simp only [toMultiset, he, ↓reduceDIte, Multiset.not_mem_zero, not_false_eq_true,
    Multiset.count_eq_zero_of_not_mem, incFun, map_zero, Finsupp.coe_zero, Pi.ofNat_apply]

@[simp]
lemma incFun_ne_zero : G.incFun e v ≠ 0 ↔ G.Inc e v := by
  classical
  rw [← toMultiset_count, Multiset.count_ne_zero, inc_iff_mem_toMultiset]

@[simp]
lemma incFun_eq_zero : G.incFun e x = 0 ↔ ¬ G.Inc e x := by
  rw [← incFun_ne_zero, not_not]

lemma Inc.iff_mem_support : G.Inc e x ↔ x ∈ (G.incFun e).support := by
  rw [Finsupp.mem_support_iff, incFun_ne_zero]


end incFun

/-! ### Extensionality -/

/-- A constructor for `Graph` in which the edge set is inferred from the incidence predicate
rather than supplied explicitly. -/
@[simps]
protected def mk' (V : Set α) (Inc₂ : β → α → α → Prop)
    (inc₂_symm : ∀ ⦃e x y⦄, Inc₂ e x y → Inc₂ e y x)
    (eq_or_eq_of_inc₂_of_inc₂ : ∀ ⦃e x y v w⦄, Inc₂ e x y → Inc₂ e v w → x = v ∨ x = w)
    (vx_mem_left_of_inc₂ : ∀ ⦃e x y⦄, Inc₂ e x y → x ∈ V) : Graph α β where
  V := V
  E := {e | ∃ x y, Inc₂ e x y}
  Inc₂ := Inc₂
  inc₂_symm := inc₂_symm
  eq_or_eq_of_inc₂_of_inc₂ := eq_or_eq_of_inc₂_of_inc₂
  edge_mem_iff_exists_inc₂ _ := Iff.rfl
  vx_mem_left_of_inc₂ := vx_mem_left_of_inc₂

@[simp]
lemma mk'_eq_self (G : Graph α β) : Graph.mk' G.V G.Inc₂ (fun _ _ _ ↦ Inc₂.symm)
  (fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq_of_inc₂ h') (fun _ _ _ ↦ Inc₂.vx_mem_left) = G := by
  have h := G.edgeSet_eq_setOf_exists_inc₂
  cases G with | mk V E Inc₂ _ _ _ => simpa [Graph.mk'] using h.symm

lemma inc_eq_inc_iff {G₁ G₂ : Graph α β} : G₁.Inc e = G₂.Inc f ↔ G₁.Inc₂ e = G₂.Inc₂ f := by
  constructor <;> rintro h
  · ext x y
    rw [inc₂_iff_inc, inc₂_iff_inc, h]
  · simp [funext_iff, inc_iff_exists_inc₂, eq_iff_iff, h]

lemma inc_iff_inc_iff {G₁ G₂ : Graph α β} :
    (∀ x, G₁.Inc e x ↔ G₂.Inc f x) ↔ (∀ x y, G₁.Inc₂ e x y ↔ G₂.Inc₂ f x y) := by
  convert inc_eq_inc_iff (G₁ := G₁) (G₂ := G₂) (e := e) (f := f) using 1 <;>
  simp_rw [funext_iff, eq_iff_iff]

lemma toMultiset_eq_toMultiset_iff {G' : Graph α β} :
    G.toMultiset e = G'.toMultiset f ↔ G.Inc₂ e = G'.Inc₂ f := by
  constructor <;> rintro h
  · ext x y
    rw [← toMultiset_eq_pair_iff, h, toMultiset_eq_pair_iff]
  · by_cases he : e ∈ G.E
    · obtain ⟨x, y, hxy⟩ := G.exists_inc₂_of_mem_edgeSet he
      rw [hxy.toMultiset, Inc₂.toMultiset (h ▸ hxy)]
    · have : f ∉ G'.E := fun h' ↦ by
        obtain ⟨x, y, hxy⟩ := G'.exists_inc₂_of_mem_edgeSet h'
        exact he (h ▸ hxy).edge_mem |>.elim
      simp [he, this]

lemma toMultiset_eq_toMultiset_iff' {G' : Graph α β} :
    G.toMultiset e = G'.toMultiset f ↔ (∀ x y, G.Inc₂ e x y ↔ G'.Inc₂ f x y) := by
  convert toMultiset_eq_toMultiset_iff (G := G) (G' := G') using 1
  simp_rw [funext_iff, eq_iff_iff]

lemma toSym2_eq_toSym2_iff {G' : Graph α β} (he : e ∈ G.E) (hf : f ∈ G'.E) :
    G.toSym2 e he = G'.toSym2 f hf ↔ G.Inc₂ e = G'.Inc₂ f := by
  obtain ⟨x, y, hxy⟩ := G.exists_inc₂_of_mem_edgeSet he
  obtain ⟨x', y', hx'y'⟩ := G'.exists_inc₂_of_mem_edgeSet hf
  rw [hxy.toSym2, Inc₂.toSym2 hx'y']
  constructor <;> rintro h
  · ext u v
    rw [hxy.inc₂_iff_sym2_eq, h, hx'y'.inc₂_iff_sym2_eq]
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (h ▸ hxy).eq_and_eq_or_eq_and_eq_of_inc₂ hx'y' <;> simp

lemma toSym2_eq_toSym2_iff' {G' : Graph α β} (he : e ∈ G.E) (hf : f ∈ G'.E) :
    G.toSym2 e he = G'.toSym2 f hf ↔ (∀ x y, G.Inc₂ e x y ↔ G'.Inc₂ f x y) := by
  convert toSym2_eq_toSym2_iff (he := he) (hf := hf) using 1
  simp_rw [funext_iff, eq_iff_iff]

/-- Two graphs with the same vertex set and binary incidences are equal. -/
@[ext]
protected lemma ext {G₁ G₂ : Graph α β} (hV : G₁.V = G₂.V)
    (h : ∀ e x y, G₁.Inc₂ e x y ↔ G₂.Inc₂ e x y) : G₁ = G₂ := by
  rw [← G₁.mk'_eq_self, ← G₂.mk'_eq_self]
  simp_rw [hV]
  convert rfl using 2
  ext
  rw [h]

/-- Two graphs with the same vertex set and unary incidences are equal. -/
lemma ext_inc {G₁ G₂ : Graph α β} (hV : G₁.V = G₂.V) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ ↦ by simp_rw [inc₂_iff_inc, h]

/-- Two graphs with the same vertex set and Multiset of edges are equal. -/
lemma ext_toMultiset {G₁ G₂ : Graph α β} (hV : G₁.V = G₂.V) (h : ∀ e, G₁.toMultiset e = G₂.toMultiset e) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ ↦ by simp_rw [← toMultiset_eq_pair_iff, h]

/-- Two graphs with the same vertex & edge sets and Sym2 of edges are equal. -/
lemma ext_toSym2 {G₁ G₂ : Graph α β} (hV : G₁.V = G₂.V) (hE : G₁.E = G₂.E)
    (h : ∀ e he, G₁.toSym2 e he = G₂.toSym2 e (hE ▸ he)) : G₁ = G₂ :=
  Graph.ext hV fun e _ _ ↦ by
    by_cases he : e ∈ G₁.E
    · simp_rw [← toSym2_eq_pair_iff he , h, toSym2_eq_pair_iff]
    · simp [he, hE ▸ he]


-- TODO: write a docstring
@[simps]
def copy (G : Graph α β) {V : Set α} {E : Set β} {Inc₂ : β → α → α → Prop} (hV : G.V = V)
    (hE : G.E = E) (h_inc₂ : ∀ e x y, G.Inc₂ e x y ↔ Inc₂ e x y) : Graph α β where
  V := V
  E := E
  Inc₂ := Inc₂
  inc₂_symm := by
    simp_rw [← h_inc₂]
    exact G.inc₂_symm
  eq_or_eq_of_inc₂_of_inc₂ := by
    simp_rw [← h_inc₂]
    exact G.eq_or_eq_of_inc₂_of_inc₂
  edge_mem_iff_exists_inc₂ := by
    simp_rw [← h_inc₂, ← hE]
    exact G.edge_mem_iff_exists_inc₂
  vx_mem_left_of_inc₂ := by
    simp_rw [← h_inc₂, ← hV]
    exact G.vx_mem_left_of_inc₂

lemma copy_eq_self (G : Graph α β) {V : Set α} {E : Set β} {Inc₂ : β → α → α → Prop}
    (hV : G.V = V) (hE : G.E = E) (h_inc₂ : ∀ e x y, G.Inc₂ e x y ↔ Inc₂ e x y) :
    G.copy hV hE h_inc₂ = G := by
  ext <;> simp_all



section Degree

/-- The degree of a vertex as a term in `ℕ∞`. -/
noncomputable def eDegree (G : Graph α β) (v : α) : ℕ∞ := ∑' e, (G.incFun e v : ℕ∞)

/-- The degree of a vertex as a term in `ℕ` (with value zero if the degree is infinite). -/
noncomputable def degree (G : Graph α β) (v : α) : ℕ := (G.eDegree v).toNat

def regular (G : Graph α β) := ∃ d, ∀ v, G.degree v = d

lemma degree_eq_fintype_sum [Fintype β] (G : Graph α β) (v : α) :
    G.degree v = ∑ e, G.incFun e v := by
  rw [degree, eDegree, tsum_eq_sum (s := Finset.univ) (by simp), ← Nat.cast_inj (R := ℕ∞),
    Nat.cast_sum, ENat.coe_toNat]
  refine WithTop.sum_ne_top.2 fun i _ ↦ ?_
  rw [← WithTop.lt_top_iff_ne_top]
  exact Batteries.compareOfLessAndEq_eq_lt.1 rfl

lemma degree_eq_edgeSet_sum (G : Graph α β) [Fintype G.E] (v : α) :
    G.degree v = ∑ e ∈ G.E, G.incFun e v := by
  rw [degree, eDegree, tsum_eq_sum (s := G.E.toFinset) (by simp; exact fun b hb ↦ not_inc_of_not_mem_edgeSet hb v), ← Nat.cast_inj (R := ℕ∞),
    Nat.cast_sum, ENat.coe_toNat]
  refine WithTop.sum_ne_top.2 fun i _ ↦ ?_
  rw [← WithTop.lt_top_iff_ne_top]
  exact Batteries.compareOfLessAndEq_eq_lt.1 rfl

lemma degree_eq_finsum [Finite β] (G : Graph α β) (v : α) :
    G.degree v = ∑ᶠ e, G.incFun e v := by
  have := Fintype.ofFinite β
  rw [degree_eq_fintype_sum, finsum_eq_sum_of_fintype]

lemma degree_eq_finsum_edgeSet (G : Graph α β) [Finite G.E] (v : α) :
    G.degree v = ∑ᶠ (e) (_ : e ∈ G.E), G.incFun e v := by
  rw [degree_eq_edgeSet_sum, finsum_cond_eq_sum_of_cond_iff (t := G.E.toFinset) (h := by simp)]

@[simp]
lemma finsum_incFun_eq (he : e ∈ G.E) : ∑ᶠ v, G.incFun e v = 2 := by
  simp_rw [← sum_incFun_eq_two he, Finsupp.sum]
  rw [finsum_eq_finset_sum_of_support_subset]
  simp

@[simp]
lemma finsum_vxSet_incFun_eq (he : e ∈ G.E) : ∑ᶠ v ∈ G.V, G.incFun e v = 2 := by
  simp_rw [← sum_incFun_eq_two he, Finsupp.sum, finsum_mem_def]
  rw [← finsum_eq_finset_sum_of_support_subset]
  refine finsum_congr fun v ↦ ?_
  rw [indicator_apply_eq_self]
  rintro hv
  simp [not_inc_of_not_mem_vxSet v hv]
  · simp

lemma handshake [Finite α] [Finite β] (G : Graph α β) :
    ∑ᶠ v, G.degree v = 2 * G.E.ncard := by
  have h := finsum_mem_comm (fun e v ↦ G.incFun e v) G.E.toFinite (Set.finite_univ (α := α))
  convert h.symm using 1
  · simp only [Set.mem_univ, finsum_true, degree_eq_finsum, finsum_mem_def]
    convert rfl with v e
    rw [indicator_apply_eq_self]
    simp only [indicator_apply_eq_self, incFun_eq_zero, not_imp_not]
    apply Inc.edge_mem
  simp only [Set.mem_univ, finsum_true]
  rw [finsum_mem_congr (show G.E = G.E from rfl) (fun x h ↦ finsum_incFun_eq h),
    finsum_mem_eq_toFinset_sum, Finset.sum_const, ncard_eq_toFinset_card]
  simp only [toFinite_toFinset, toFinset_card, mul_comm, smul_eq_mul]

lemma handshake' (G : Graph α β) [hV : Finite G.V] [hE : Finite G.E] :
    ∑ᶠ v, G.degree v = 2 * G.E.ncard := by
  have h := finsum_mem_comm (fun e v ↦ G.incFun e v) G.E.toFinite hV
  convert h.symm using 1
  · simp only [degree_eq_finsum_edgeSet, finsum_mem_def]
    convert rfl with v
    rw [indicator_apply_eq_self]
    rintro hv
    convert finsum_zero with e
    simp [not_inc_of_not_mem_vxSet v hv]
  simp only [Set.mem_univ, finsum_true]
  rw [finsum_mem_congr (show G.E = G.E from rfl) (fun x h ↦ finsum_vxSet_incFun_eq h),
    finsum_mem_eq_toFinset_sum, Finset.sum_const, ncard_eq_toFinset_card _ hE]
  simp only [toFinite_toFinset, toFinset_card, mul_comm, smul_eq_mul]

end Degree

section Isolated

def Isolated (G : Graph α β) (v : α) := ∀ e, ¬ G.Inc e v

namespace Isolated

lemma not_adj_left (hisol : G.Isolated u) : ¬ G.Adj u v := by
  rintro ⟨e, hbtw⟩
  exact hisol e hbtw.inc_left

lemma not_adj_right (hisol : G.Isolated u) : ¬ G.Adj v u := by
  rw [adj_comm]
  exact hisol.not_adj_left

lemma not_inc₂_left (hisol : G.Isolated u) : ¬ G.Inc₂ e u v :=
  (hisol e ·.inc_left)

lemma not_inc₂_right (hisol : G.Isolated u) : ¬ G.Inc₂ e v u :=
  (hisol e ·.inc_right)

end Isolated

lemma isolated_of_E_empty (hE : G.E = ∅) : G.Isolated u := by
  intro e hinc
  exact (hE ▸ hinc.edge_mem : e ∈ ∅)

lemma degree_eq_zero_iff_isolated (G : Graph α β) [Finite G.E] (v : α) :
    G.degree v = 0 ↔ G.Isolated v := by
  rw [degree_eq_edgeSet_sum]
  constructor <;> rintro h
  · intro e
    contrapose! h
    simp only [ne_eq, Finset.sum_eq_zero_iff, mem_toFinset, incFun_eq_zero, not_forall,
      Classical.not_imp, not_not]
    use e, h.edge_mem
  · simp only [Finset.sum_eq_zero_iff, mem_toFinset, incFun_eq_zero]
    exact fun i _ ↦ h i

end Isolated
end Graph
