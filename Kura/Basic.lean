/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
import Mathlib.Data.Sym.Sym2
import Mathlib.Topology.Instances.ENat
import Kura.Dep.Finset
import Kura.Dep.Sym2
import Canonical

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

* `V(G)` denotes the vertex set of `G` as a term in `Set α`.
* `E(G)` denotes the edge set of `G` as a term in `Set β`.
* `G.IsLink e x y` means that the edge `e : β` has vertices `x : α` and `y : α` as its ends.
* `G.Inc e x` means that the edge `e : β` has `x` as one of its ends.
* `G.Adj x y` means that there is an edge `e` having `x` and `y` as its ends.
* `G.IsLoopAt e x` means that `e` is a loop edge with both ends equal to `x`.
* `G.IsNonloopAt e x` means that `e` is a non-loop edge with one end equal to `x`.

## Implementation notes

Unlike the design of `SimpleGraph`, the vertex and edge sets of `G` are modelled as sets
`V(G) : Set α` and `E(G) : Set β`, within ambient types, rather than being types themselves.
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

Relecting written mathematics, we use the compact notations `V(G)` and `E(G)` to describe
vertex and edge sets formally, but use the longer terms `vertexSet` and `edgeSet` within
lemma names to refer to the same objects.

-/

variable {α β : Type*} {x y z u v w : α} {e f : β}

open Set

/-- A multigraph with vertex set `V : Set α` and edge set `E : Set β`,
as described by a predicate describing whether an edge `e : β` has ends `x` and `y`. -/
structure Graph (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  /-- The edge set. -/
  edgeSet : Set β
  /-- The predicate that an edge `e` goes from `x` to `y`. -/
  IsLink : β → α → α → Prop
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e x y⦄, IsLink e x y → IsLink e y x
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w
  /-- If `e` is incident to something, then `e` is in the edge set -/
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  vx_mem_left_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet

initialize_simps_projections Graph (vertexSet → vertexSet, edgeSet → edgeSet, IsLink → isLink)

namespace Graph

scoped notation "V(" G ")" => Graph.vertexSet G
scoped notation "E(" G ")" => Graph.edgeSet G

variable {G H : Graph α β}

/-! ### Edge-vertex-vertex incidence -/

lemma IsLink.symm (h : G.IsLink e x y) : G.IsLink e y x :=
  G.isLink_symm h

lemma isLink_comm : G.IsLink e x y ↔ G.IsLink e y x :=
  ⟨IsLink.symm, IsLink.symm⟩

lemma IsLink.edge_mem (h : G.IsLink e x y) : e ∈ E(G) :=
  (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩

lemma IsLink.vx_mem_left (h : G.IsLink e x y) : x ∈ V(G) :=
  G.vx_mem_left_of_isLink h

lemma IsLink.vx_mem_right (h : G.IsLink e x y) : y ∈ V(G) :=
  h.symm.vx_mem_left

lemma exists_isLink_of_mem_edgeSet (h : e ∈ E(G)) : ∃ x y, G.IsLink e x y :=
  (edge_mem_iff_exists_isLink ..).1 h

lemma IsLink.left_eq_or_eq_of_isLink (h : G.IsLink e x y) (h' : G.IsLink e z w) : x = z ∨ x = w :=
  G.eq_or_eq_of_isLink_of_isLink h h'

lemma IsLink.left_eq_of_isLink_of_ne (h : G.IsLink e x y) (h' : G.IsLink e z w) (hzx : x ≠ z) : x = w :=
  (h.left_eq_or_eq_of_isLink h').elim (False.elim ∘ hzx) id

lemma IsLink.eq_of_isLink (h : G.IsLink e x y) (h' : G.IsLink e x z) : y = z := by
  obtain rfl | rfl := h.symm.left_eq_or_eq_of_isLink h'.symm; rfl
  obtain rfl | rfl := h'.symm.left_eq_or_eq_of_isLink h.symm <;> rfl

lemma IsLink.isLink_iff_eq (h : G.IsLink e x y) : G.IsLink e x z ↔ z = y :=
  ⟨fun h' ↦ h'.eq_of_isLink h, fun h' ↦ h' ▸ h⟩

lemma edgeSet_eq_setOf_exists_isLink : E(G) = {e | ∃ x y, G.IsLink e x y} :=
  Set.ext fun e ↦ G.edge_mem_iff_exists_isLink e

@[simp]
lemma not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) (x y : α) : ¬ G.IsLink e x y := by
  contrapose! he
  exact he.edge_mem

@[simp]
lemma not_isLink_of_left_notMem_vertexSet (x : α) (hx : x ∉ V(G)) : ¬ G.IsLink e x y := by
  contrapose! hx
  exact hx.vx_mem_left

@[simp]
lemma not_isLink_of_right_notMem_vertexSet (y : α) (hy : y ∉ V(G)) : ¬ G.IsLink e x y := by
  contrapose! hy
  exact hy.vx_mem_right

lemma IsLink.isLink_iff_eq_left {x' : α} (h : G.IsLink e x y) : G.IsLink e x' y ↔ x = x' := by
  constructor
  · rintro h'
    obtain rfl | rfl := h.left_eq_or_eq_of_isLink h'
    · rfl
    obtain rfl | rfl := h'.left_eq_or_eq_of_isLink h <;> rfl
  · rintro rfl
    exact h

lemma IsLink.isLink_iff_eq_right {y' : α} (h : G.IsLink e x y) : G.IsLink e x y' ↔ y = y' := by
  rw [isLink_comm, h.symm.isLink_iff_eq_left]

lemma IsLink.eq_and_eq_or_eq_and_eq_of_isLink {x' y' : α} (h : G.IsLink e x y) (h' : G.IsLink e x' y') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  obtain rfl | rfl := h.left_eq_or_eq_of_isLink h'
  on_goal 1 => obtain rfl := h.isLink_iff_eq_right.mp h'
  on_goal 2 => obtain rfl := h.symm.isLink_iff_eq_left.mp h'
  all_goals tauto

lemma IsLink.isLink_iff (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  refine ⟨h.eq_and_eq_or_eq_and_eq_of_isLink, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl,rfl⟩)
  · assumption
  exact h.symm

lemma IsLink.isLink_iff_sym2_eq (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ s(x,y) = s(x',y') := by
  rw [h.isLink_iff, Sym2.eq_iff]

/-! ### Edge-vertex incidence -/

/-- `G.Inc e x` means that `x` is one of the ends of `e`. -/
def Inc (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, G.IsLink e x y

lemma inc_iff_exists_isLink : G.Inc e x ↔ ∃ y, G.IsLink e x y := Iff.rfl
alias ⟨Inc.exists_vx_isLink, _⟩ := inc_iff_exists_isLink

@[simp]
lemma Inc.edge_mem (h : G.Inc e x) : e ∈ E(G) :=
  h.choose_spec.edge_mem

@[simp]
lemma Inc.vx_mem (h : G.Inc e x) : x ∈ V(G) :=
  h.choose_spec.vx_mem_left

@[simp]
lemma IsLink.inc_left (h : G.IsLink e x y) : G.Inc e x :=
  ⟨y, h⟩

@[simp]
lemma IsLink.inc_right (h : G.IsLink e x y) : G.Inc e y :=
  ⟨x, h.symm⟩

lemma Inc.eq_or_eq_of_isLink (h : G.Inc e x) (h' : G.IsLink e y z) : x = y ∨ x = z :=
  h.choose_spec.left_eq_or_eq_of_isLink h'

lemma IsLink.eq_or_eq_of_inc (h : G.IsLink e x y) (h' : G.Inc e z) : x = z ∨ y = z := by
  have := h'.eq_or_eq_of_isLink h
  tauto

lemma Inc.eq_of_isLink_of_ne_left (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : x ≠ y) : x = z :=
  (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id

@[simp]
lemma not_inc_of_notMem_edgeSet (he : e ∉ E(G)) (x : α) : ¬ G.Inc e x :=
  (he ·.edge_mem)

@[simp]
lemma not_inc_of_notMem_vertexSet (x : α) (hx : x ∉ V(G)) : ¬ G.Inc e x := by
  contrapose! hx
  exact hx.vx_mem

lemma exists_inc_of_mem_edgeSet (he : e ∈ E(G)) : ∃ x, G.Inc e x := by
  obtain ⟨y, z, h⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨y, h.inc_left⟩

/-- Given a proof that `e` is incident with `x`, noncomputably find the other end of `e`.
(If `e` is a loop, this is equal to `x` itself). -/
noncomputable def Inc.other (h : G.Inc e x) : α := h.choose

@[simp]
lemma Inc.isLink_other (h : G.Inc e x) : G.IsLink e x h.other :=
  h.choose_spec

@[simp]
lemma Inc.inc_other (h : G.Inc e x) : G.Inc e h.other :=
  h.isLink_other.inc_right

lemma Inc.eq_or_eq_or_eq_of_inc_of_inc (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  by_contra! hcon
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_isLink_of_ne_left hx' hcon.1.symm
  obtain rfl := hz.eq_of_isLink_of_ne_left hx' hcon.2.1.symm
  exact hcon.2.2 rfl

/-- The binary incidence predicate can be expressed in terms of the unary one. -/
lemma isLink_iff_inc : G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.eq_or_eq_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq_of_isLink hy'
    · assumption
    exact hy'.symm
  assumption

lemma Inc.isLink_of_inc_of_ne (h : G.Inc e x) (h' : G.Inc e y) (hxy : x ≠ y) : G.IsLink e x y := by
  obtain ⟨z, hz⟩ := h
  obtain rfl | rfl := hz.eq_or_eq_of_inc h'
  · simp at hxy
  exact hz

/-- `G.IsLoopAt e x` means that `e` is a loop edge at the vertex `x`. -/
def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.IsLink e x x

lemma isLink_self_iff : G.IsLink e x x ↔ G.IsLoopAt e x := Iff.rfl

lemma IsLoopAt.isLink (h : G.IsLoopAt e x) : G.IsLink e x x := h

lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x :=
  IsLink.inc_left h

lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

lemma IsLoopAt.isLink_iff_eq (h : G.IsLoopAt e x) : G.IsLink e x y ↔ x = y :=
  ⟨h.eq_of_isLink, fun h' ↦ by rwa [← h']⟩

@[simp]
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

@[simp]
lemma IsLoopAt.vx_mem (h : G.IsLoopAt e x) : x ∈ V(G) :=
  h.inc.vx_mem

/-- `G.IsNonloopAt e x` means that `e` is an edge from `x` to some `y ≠ x`. -/
@[mk_iff]
structure IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop where
  inc : G.Inc e x
  exists_isLink_ne : ∃ y ≠ x, G.IsLink e x y

@[simp]
lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

@[simp]
lemma IsNonloopAt.vx_mem (h : G.IsNonloopAt e x) : x ∈ V(G) :=
  h.inc.vx_mem

lemma IsLoopAt.not_isNonloop_at (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  intro h'
  obtain ⟨z, hyz, hy⟩ := h'.exists_isLink_ne
  rw [← h.eq_of_inc hy.inc_left, ← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl

lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y :=
  fun h' ↦ h'.not_isNonloop_at x h

lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  obtain ⟨y, hy⟩ := h
  obtain rfl | hne := eq_or_ne x y
  · exact .inl hy
  exact .inr ⟨hy.inc_left, y, hne.symm, hy⟩

lemma Inc.isLoopAt_or_isLink_ne (h : G.Inc e x) : G.IsLoopAt e x ∨ ∃ y ≠ x, G.IsLink e x y := by
  obtain ⟨y, hy⟩ := h
  obtain rfl | hne := eq_or_ne x y
  · exact .inl hy
  exact .inr ⟨y, hne.symm, hy⟩

lemma IsLink.isNonloopAt_iff_ne (h : G.IsLink e x y) : G.IsNonloopAt e x ↔ x ≠ y := by
  obtain rfl | hne := eq_or_ne x y
  · exact iff_of_false (IsLoopAt.not_isNonloop_at h x) <| by simp
  rw [isNonloopAt_iff]
  exact iff_of_true ⟨h.inc_left, ⟨y, hne.symm, h⟩⟩ hne

lemma IsLink.isNonloopAt_of_ne (h : G.IsLink e x y) (hxy : x ≠ y) : G.IsNonloopAt e x :=
  h.isNonloopAt_iff_ne.2 hxy

lemma IsLink.isNonloopAt_right_of_ne (h : G.IsLink e x y) (hxy : x ≠ y) : G.IsNonloopAt e y :=
  h.symm.isNonloopAt_iff_ne.2 hxy.symm

lemma exists_isLoopAt_or_isLink_of_mem_edgeSet (h : e ∈ E(G)) :
    (∃ x, G.IsLoopAt e x) ∨ ∃ x y, G.IsLink e x y ∧ x ≠ y := by
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  obtain rfl | hne := eq_or_ne x y
  · exact .inl ⟨x, h⟩
  exact .inr ⟨x, y, h, hne⟩

/-! ### Adjacency -/

/-- `G.Adj x y` means that `G` has an edge from `x` to `y`. -/
def Adj (G : Graph α β) (x y : α) : Prop := ∃ e, G.IsLink e x y

lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩

lemma adj_comm : G.Adj x y ↔ G.Adj y x :=
  ⟨Adj.symm, Adj.symm⟩

@[simp]
lemma Adj.mem_left (h : G.Adj x y) : x ∈ V(G) :=
  h.choose_spec.vx_mem_left

@[simp]
lemma Adj.mem_right (h : G.Adj x y) : y ∈ V(G) :=
  h.symm.mem_left

lemma IsLink.adj (h : G.IsLink e x y) : G.Adj x y :=
  ⟨e, h⟩

lemma not_adj_of_left_notMem_vertexSet (x : α) (hx : x ∉ V(G)) : ¬ G.Adj x y := by
  contrapose! hx
  exact hx.mem_left

lemma not_adj_of_right_notMem_vertexSet (y : α) (hy : y ∉ V(G)) : ¬ G.Adj x y := by
  contrapose! hy
  exact hy.mem_right

/-! ### Multiset/Sym2 incidence functions -/

section toMultiset

noncomputable def toMultiset (G : Graph α β) (e : β) : Multiset α := by
  classical
  exact if he : e ∈ E(G)
    then {G.exists_isLink_of_mem_edgeSet he |>.choose,
          G.exists_isLink_of_mem_edgeSet he |>.choose_spec.choose}
    else 0

@[simp]
lemma vx_mem_of_mem_toMultiset (hxe : x ∈ G.toMultiset e) : x ∈ V(G) := by
  simp only [toMultiset] at hxe
  split_ifs at hxe with he
  · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hxe
    obtain rfl | rfl := hxe
    · exact (G.exists_isLink_of_mem_edgeSet he).choose_spec.choose_spec.vx_mem_left
    · exact (G.exists_isLink_of_mem_edgeSet he).choose_spec.choose_spec.vx_mem_right
  · exact (Multiset.notMem_zero _ hxe).elim

@[simp]
lemma edge_mem_of_mem_toMultiset (hxe : x ∈ G.toMultiset e) : e ∈ E(G) := by
  simp only [toMultiset] at hxe
  split_ifs at hxe with he
  · exact (G.exists_isLink_of_mem_edgeSet he).choose_spec.choose_spec.edge_mem
  · exact (Multiset.notMem_zero _ hxe).elim

@[simp]
lemma toMultiset_card_eq_two (he : e ∈ E(G)) : (G.toMultiset e).card = 2 := by
  simp only [toMultiset, he, ↓reduceDIte, Multiset.insert_eq_cons, Multiset.card_cons,
    Multiset.card_singleton, Nat.reduceAdd]

@[simp]
lemma toMultiset_eq_zero (he : e ∉ E(G)) : G.toMultiset e = 0 := by
  simp only [toMultiset, he, ↓reduceDIte]

@[simp]
lemma toMultiset_eq_zero_iff : G.toMultiset e = 0 ↔ e ∉ E(G) := by
  refine ⟨fun h he ↦ ?_, toMultiset_eq_zero⟩
  have := h ▸ toMultiset_card_eq_two he
  simp at this

@[simp]
lemma toMultiset_card_eq_two_iff : (G.toMultiset e).card = 2 ↔ e ∈ E(G) := by
  refine ⟨fun h ↦ ?_, fun he ↦ ?_⟩
  · rw [Multiset.card_eq_two] at h
    obtain ⟨x, y, hxy⟩ := h
    exact edge_mem_of_mem_toMultiset (by rw [hxy]; simp : x ∈ G.toMultiset e)
  · rw [toMultiset_card_eq_two he]

lemma toMultiset_card_or : (G.toMultiset e).card = 2 ∨ (G.toMultiset e).card = 0 := by
  by_cases he : e ∈ E(G)
  · exact Or.inl (toMultiset_card_eq_two_iff.mpr he)
  · exact Or.inr (Multiset.card_eq_zero.mpr (toMultiset_eq_zero_iff.mpr he))

@[simp]
lemma toMultiset_eq_pair_iff : G.toMultiset e = {x, y} ↔ G.IsLink e x y := by
  constructor <;> rintro h
  · have he := edge_mem_of_mem_toMultiset (by rw [h]; simp : x ∈ G.toMultiset e)
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := by simpa only [toMultiset, he, ↓reduceDIte, Multiset.pair_eq_pair_iff] using h
    · exact (G.exists_isLink_of_mem_edgeSet he).choose_spec.choose_spec
    · exact (G.exists_isLink_of_mem_edgeSet he).choose_spec.choose_spec.symm
  · simp only [Graph.toMultiset, h.edge_mem, ↓reduceDIte]
    let huv := (G.exists_isLink_of_mem_edgeSet h.edge_mem).choose_spec.choose_spec
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := huv.eq_and_eq_or_eq_and_eq_of_isLink h <;> simp_rw [← h1, ← h2]
    rw [Multiset.pair_comm]

alias ⟨_, IsLink.toMultiset⟩ := toMultiset_eq_pair_iff

@[simp]
lemma inc_iff_mem_toMultiset : x ∈ G.toMultiset e ↔ G.Inc e x := by
  constructor
  · rintro h
    obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet (edge_mem_of_mem_toMultiset h)
    simp only [huv.toMultiset, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h
    obtain rfl | rfl := h
    · exact huv.inc_left
    · exact huv.inc_right
  · rintro ⟨y, h⟩
    simp [h.toMultiset]

alias ⟨_, Inc.mem_toMultiset⟩ := inc_iff_mem_toMultiset

end toMultiset

section toSym2

noncomputable def toSym2 (G : Graph α β) (e : β) (he : e ∈ E(G)) : Sym2 α :=
  s(G.exists_isLink_of_mem_edgeSet he |>.choose, G.exists_isLink_of_mem_edgeSet he |>.choose_spec.choose)

@[simp]
lemma vx_mem_of_toSym2 {he : e ∈ E(G)} (h : x ∈ G.toSym2 e he) : x ∈ V(G) := by
  have := (G.exists_isLink_of_mem_edgeSet he).choose_spec.choose_spec
  obtain rfl | rfl := by simpa [toSym2] using h
  · exact this.vx_mem_left
  · exact this.vx_mem_right

@[simp]
lemma toSym2_eq_pair_iff (he : e ∈ E(G)) : G.toSym2 e he = s(x, y) ↔ G.IsLink e x y := by
  have := (G.exists_isLink_of_mem_edgeSet he).choose_spec.choose_spec
  constructor <;> rintro h
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := by simpa [toSym2] using h
    · exact this
    · exact this.symm
  · simpa [toSym2] using this.eq_and_eq_or_eq_and_eq_of_isLink h

lemma IsLink.toSym2 (h : G.IsLink e x y) : G.toSym2 e h.edge_mem = s(x, y) := by
  rwa [toSym2_eq_pair_iff h.edge_mem]

noncomputable def func (G : Graph α β) (e : E(G)) : Sym2 V(G) :=
  let H := G.exists_isLink_of_mem_edgeSet e.prop
  s(⟨H.choose, H.choose_spec.choose_spec.vx_mem_left⟩,
    ⟨H.choose_spec.choose, H.choose_spec.choose_spec.vx_mem_right⟩)

@[simp] lemma func_eq_pair_iff {x y : V(G)} {e : E(G)} :
    G.func e = s(x, y) ↔ G.IsLink e x y := by
  let H := G.exists_isLink_of_mem_edgeSet e.prop
  let a := H.choose
  let b := H.choose_spec.choose
  let h := H.choose_spec.choose_spec
  simp only [func]
  change s(⟨a, h.vx_mem_left⟩, ⟨b, h.vx_mem_right⟩) = s(x, y) ↔ G.IsLink e x y
  constructor <;> rintro hbtw
  · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hbtw
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hbtw
    · exact H.choose_spec.choose_spec
    · exact H.choose_spec.choose_spec.symm
  · simp [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, Subtype.ext_iff]
    exact h.eq_and_eq_or_eq_and_eq_of_isLink hbtw

lemma IsLink.func (h : G.IsLink e x y) :
    G.func ⟨e, h.edge_mem⟩ = s(⟨x, h.vx_mem_left⟩, ⟨y, h.vx_mem_right⟩) := by simpa

lemma exists_func_pair (e : E(G)) : ∃ x y, G.func e = s(x, y) := by
  let H := G.exists_isLink_of_mem_edgeSet e.prop
  let a := H.choose
  let b := H.choose_spec.choose
  let h := H.choose_spec.choose_spec
  exact ⟨⟨a, h.vx_mem_left⟩, ⟨b, h.vx_mem_right⟩, H.choose_spec.choose_spec.func⟩

lemma val_func_eq_toSym2 {e : β} (he : e ∈ E(G)) : (G.func ⟨e, he⟩).map Subtype.val = G.toSym2 e he := by
  rw [(G.func ⟨e, he⟩).eq_mk_out, eq_comm, Sym2.map_pair_eq, toSym2_eq_pair_iff]
  change G.IsLink (⟨e, he⟩ : E(G)) _ _
  rw [← func_eq_pair_iff]
  exact (G.func ⟨e, he⟩).eq_mk_out

end toSym2

section incFun

noncomputable def incFun (G : Graph α β) (e : β) : α →₀ ℕ := by
  classical
  exact (G.toMultiset e).toFinsupp

lemma IsLink.incFun_support_eq [DecidableEq α] (h : G.IsLink e x y) :
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

lemma incFun_eq_zero_of_notMem (he : e ∉ E(G)) : G.incFun e = 0 := by
  simp [DFunLike.ext_iff, incFun, inc_iff_exists_isLink, not_isLink_of_notMem_edgeSet he]

lemma incFun_le_two (G : Graph α β) (e : β) (x : α) : G.incFun e x ≤ 2 := by
  classical
  obtain ⟨y, hy⟩ | hx := em <| G.Inc e x
  · rw [incFun, Multiset.toFinsupp_apply, ← toMultiset_card_eq_two_iff.mpr (hy.edge_mem)]
    exact Multiset.count_le_card x _
  simp [incFun, isLink_iff_inc, hx]

lemma IsNonloopAt.IncFun_eq_one (h : G.IsNonloopAt e x) : G.incFun e x = 1 := by
  obtain ⟨y, hne, hxy⟩ := h.exists_isLink_ne
  rw [← toMultiset_eq_pair_iff] at hxy
  simp [incFun, hxy, hne.symm]

@[simp]
lemma incFun_eq_one_iff : G.incFun e x = 1 ↔ G.IsNonloopAt e x := by
  obtain (⟨y, hxy⟩ | hex) := em <| G.Inc e x
  · simp [hxy.isNonloopAt_iff_ne, incFun, toMultiset_eq_pair_iff.mpr hxy]
  simp [incFun, mt IsLink.inc_left hex, mt IsNonloopAt.inc hex]
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
    isLink_self_iff, hxy.isLink_iff_eq_right]
    exact eq_comm
  simp [incFun, mt IsLink.inc_left hex, hex, mt IsLoopAt.inc hex]

lemma IsLoopAt.incFun_eq_two (h : G.IsLoopAt e x) : G.incFun e x = 2 :=
  incFun_eq_two_iff.2 h

@[simp]
lemma incFun_eq_zero_iff : G.incFun e = 0 ↔ e ∉ E(G) := by
  refine ⟨fun h he ↦ ?_, incFun_eq_zero_of_notMem⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  obtain hx | hx := hxy.inc_left.isLoopAt_or_isNonloopAt
  · have := h ▸ hx.incFun_eq_two
    simp at this
  have := h ▸ hx.incFun_eq_one
  simp at this

lemma sum_incFun_eq_two (he : e ∈ E(G)) : (G.incFun e).sum (fun _ x ↦ x) = 2 := by
  classical
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  obtain rfl | hne := eq_or_ne x y
  · simp [Finsupp.sum, hxy.incFun_support_eq, hxy.isLink_iff_eq, show G.IsLoopAt e x from hxy]
  simp [Finsupp.sum, hxy.incFun_support_eq, Finset.sum_pair hne,
    (hxy.isNonloopAt_of_ne hne).incFun_eq_one, (hxy.isNonloopAt_right_of_ne hne).incFun_eq_one]

@[simp]
lemma toMultiset_count [DecidableEq α] (x : α) : (G.toMultiset e).count x = G.incFun e x := by
  classical
  by_cases he : e ∈ E(G)
  · simp only [toMultiset, he, ↓reduceDIte, incFun]
    convert (Multiset.toFinsupp_apply _ x).symm
  · simp only [toMultiset, he, ↓reduceDIte, Multiset.notMem_zero, not_false_eq_true,
    Multiset.count_eq_zero_of_notMem, incFun, map_zero, Finsupp.coe_zero, Pi.ofNat_apply]

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
protected def mk' (V : Set α) (IsLink : β → α → α → Prop)
    (isLink_symm : ∀ ⦃e x y⦄, IsLink e x y → IsLink e y x)
    (eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w)
    (vx_mem_left_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ V) : Graph α β where
  vertexSet := V
  edgeSet := {e | ∃ x y, IsLink e x y}
  IsLink := IsLink
  isLink_symm := isLink_symm
  eq_or_eq_of_isLink_of_isLink := eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink _ := Iff.rfl
  vx_mem_left_of_isLink := vx_mem_left_of_isLink

@[simp]
lemma mk'_eq_self (G : Graph α β) : Graph.mk' V(G) G.IsLink (fun _ _ _ ↦ IsLink.symm)
  (fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq_of_isLink h') (fun _ _ _ ↦ IsLink.vx_mem_left) = G := by
  have h := G.edgeSet_eq_setOf_exists_isLink
  cases G with | mk V E IsLink _ _ _ => simpa [Graph.mk'] using h.symm

lemma inc_eq_inc_iff {G₁ G₂ : Graph α β} : G₁.Inc e = G₂.Inc f ↔ G₁.IsLink e = G₂.IsLink f := by
  constructor <;> rintro h
  · ext x y
    rw [isLink_iff_inc, isLink_iff_inc, h]
  · simp [funext_iff, inc_iff_exists_isLink, eq_iff_iff, h]

lemma inc_iff_inc_iff {G₁ G₂ : Graph α β} :
    (∀ x, G₁.Inc e x ↔ G₂.Inc f x) ↔ (∀ x y, G₁.IsLink e x y ↔ G₂.IsLink f x y) := by
  convert inc_eq_inc_iff (G₁ := G₁) (G₂ := G₂) (e := e) (f := f) using 1 <;>
  simp_rw [funext_iff, eq_iff_iff]

lemma toMultiset_eq_toMultiset_iff {G' : Graph α β} :
    G.toMultiset e = G'.toMultiset f ↔ G.IsLink e = G'.IsLink f := by
  constructor <;> rintro h
  · ext x y
    rw [← toMultiset_eq_pair_iff, h, toMultiset_eq_pair_iff]
  · by_cases he : e ∈ E(G)
    · obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      rw [hxy.toMultiset, IsLink.toMultiset (h ▸ hxy)]
    · have : f ∉ E(G') := fun h' ↦ by
        obtain ⟨x, y, hxy⟩ := G'.exists_isLink_of_mem_edgeSet h'
        exact he (h ▸ hxy).edge_mem |>.elim
      simp [he, this]

lemma toMultiset_eq_toMultiset_iff' {G' : Graph α β} :
    G.toMultiset e = G'.toMultiset f ↔ (∀ x y, G.IsLink e x y ↔ G'.IsLink f x y) := by
  convert toMultiset_eq_toMultiset_iff (G := G) (G' := G') using 1
  simp_rw [funext_iff, eq_iff_iff]

lemma toSym2_eq_toSym2_iff {G' : Graph α β} (he : e ∈ E(G)) (hf : f ∈ E(G')) :
    G.toSym2 e he = G'.toSym2 f hf ↔ G.IsLink e = G'.IsLink f := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  obtain ⟨x', y', hx'y'⟩ := G'.exists_isLink_of_mem_edgeSet hf
  rw [hxy.toSym2, IsLink.toSym2 hx'y']
  constructor <;> rintro h
  · ext u v
    rw [hxy.isLink_iff_sym2_eq, h, hx'y'.isLink_iff_sym2_eq]
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (h ▸ hxy).eq_and_eq_or_eq_and_eq_of_isLink hx'y' <;> simp

lemma toSym2_eq_toSym2_iff' {G' : Graph α β} (he : e ∈ E(G)) (hf : f ∈ E(G')) :
    G.toSym2 e he = G'.toSym2 f hf ↔ (∀ x y, G.IsLink e x y ↔ G'.IsLink f x y) := by
  convert toSym2_eq_toSym2_iff (he := he) (hf := hf) using 1
  simp_rw [funext_iff, eq_iff_iff]

/-- Two graphs with the same vertex set and binary incidences are equal. -/
@[ext]
protected lemma ext {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂))
    (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
  rw [← G₁.mk'_eq_self, ← G₂.mk'_eq_self]
  simp_rw [hV]
  convert rfl using 2
  ext
  rw [h]

/-- Two graphs with the same vertex set and unary incidences are equal. -/
lemma ext_inc {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ ↦ by simp_rw [isLink_iff_inc, h]

/-- Two graphs with the same vertex set and Multiset of edges are equal. -/
lemma ext_toMultiset {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : ∀ e, G₁.toMultiset e = G₂.toMultiset e) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ ↦ by simp_rw [← toMultiset_eq_pair_iff, h]

/-- Two graphs with the same vertex & edge sets and Sym2 of edges are equal. -/
lemma ext_toSym2 {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (hE : E(G₁) = E(G₂))
    (h : ∀ e he, G₁.toSym2 e he = G₂.toSym2 e (hE ▸ he)) : G₁ = G₂ :=
  Graph.ext hV fun e _ _ ↦ by
    by_cases he : e ∈ E(G₁)
    · simp_rw [← toSym2_eq_pair_iff he , h, toSym2_eq_pair_iff]
    · simp [he, hE ▸ he]


-- TODO: write a docstring
@[simps]
def copy (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β → α → α → Prop} (hV : V(G) = V)
    (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) : Graph α β where
  vertexSet := V
  edgeSet := E
  IsLink := IsLink
  isLink_symm := by
    simp_rw [← h_isLink]
    exact G.isLink_symm
  eq_or_eq_of_isLink_of_isLink := by
    simp_rw [← h_isLink]
    exact G.eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := by
    simp_rw [← h_isLink, ← hE]
    exact G.edge_mem_iff_exists_isLink
  vx_mem_left_of_isLink := by
    simp_rw [← h_isLink, ← hV]
    exact G.vx_mem_left_of_isLink

lemma copy_eq_self (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β → α → α → Prop}
    (hV : V(G) = V) (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    G.copy hV hE h_isLink = G := by
  ext <;> simp_all



section Degree

/-- The degree of a vertex as a term in `ℕ∞`. -/
noncomputable def eDegree (G : Graph α β) (v : α) : ℕ∞ := ∑' e, (G.incFun e v : ℕ∞)

/-- The degree of a vertex as a term in `ℕ` (with value zero if the degree is infinite). -/
noncomputable def degree (G : Graph α β) (v : α) : ℕ := (G.eDegree v).toNat

def regular (G : Graph α β) := ∃ d, ∀ v, G.degree v = d

lemma degree_eq_edgeSet_sum (G : Graph α β) [Fintype E(G)] (v : α) :
    G.degree v = ∑ e ∈ E(G), G.incFun e v := by
  rw [degree, eDegree, tsum_eq_sum (s := E(G).toFinset) (by simp; exact fun b hb ↦ not_inc_of_notMem_edgeSet hb v), ← Nat.cast_inj (R := ℕ∞),
    Nat.cast_sum, ENat.coe_toNat]
  refine WithTop.sum_ne_top.2 fun i _ ↦ ?_
  rw [← WithTop.lt_top_iff_ne_top]
  exact Batteries.compareOfLessAndEq_eq_lt.1 rfl

lemma degree_eq_finsum_edgeSet (G : Graph α β) [Finite E(G)] (v : α) :
    G.degree v = ∑ᶠ (e) (_ : e ∈ E(G)), G.incFun e v := by
  rw [degree_eq_edgeSet_sum, finsum_cond_eq_sum_of_cond_iff (t := E(G).toFinset) (h := by simp)]

@[simp]
lemma finsum_vertexSet_incFun_eq (he : e ∈ E(G)) : ∑ᶠ v ∈ V(G), G.incFun e v = 2 := by
  simp_rw [← sum_incFun_eq_two he, Finsupp.sum, finsum_mem_def]
  rw [← finsum_eq_finset_sum_of_support_subset]
  refine finsum_congr fun v ↦ ?_
  rw [indicator_apply_eq_self]
  rintro hv
  simp [not_inc_of_notMem_vertexSet v hv]
  · simp

lemma handshake (G : Graph α β) [hV : Finite V(G)] [hE : Finite E(G)] :
    ∑ᶠ v, G.degree v = 2 * E(G).ncard := by
  have h := finsum_mem_comm (fun e v ↦ G.incFun e v) E(G).toFinite hV
  convert h.symm using 1
  · simp only [degree_eq_finsum_edgeSet, finsum_mem_def]
    convert rfl with v
    rw [indicator_apply_eq_self]
    rintro hv
    convert finsum_zero with e
    simp [not_inc_of_notMem_vertexSet v hv]
  simp only [Set.mem_univ, finsum_true]
  rw [finsum_mem_congr (show E(G) = E(G) from rfl) (fun x h ↦ finsum_vertexSet_incFun_eq h),
    finsum_mem_eq_toFinset_sum, Finset.sum_const, ncard_eq_toFinset_card _ hE]
  simp only [toFinite_toFinset, toFinset_card, mul_comm, smul_eq_mul]

@[simp]
lemma degree_eq_zero_notMem (G : Graph α β) (hv : v ∉ V(G)) : G.degree v = 0 := by
  unfold degree eDegree
  simp only [ENat.toNat_eq_zero]
  left
  convert tsum_zero
  simp [hv]

noncomputable def maxDegree (G : Graph α β) [Finite V(G)] [Finite E(G)] : ℕ :=
  (G.degree '' V(G)).toFinset.max.unbotD 0

scoped notation "Δ(" G ")" => maxDegree G

lemma degree_le_maxDegree (G : Graph α β) [Finite V(G)] [Finite E(G)] (v : α) :
    G.degree v ≤ Δ(G) := by
  obtain hv | hv := (em <| v ∈ V(G)).symm
  · simp only [hv, not_false_eq_true, degree_eq_zero_notMem, zero_le]
  unfold maxDegree
  have hmem : G.degree v ∈ (G.degree '' V(G)).toFinset := by
    simp
    use v
  obtain ⟨e, he⟩ := Finset.max_of_mem hmem
  rw [he]
  simp only [WithBot.unbotD_coe, ge_iff_le]
  have := Finset.le_max hmem
  simp_all only [toFinset_image, WithBot.coe_le_coe]

lemma exists_vertex_maxDegree (G : Graph α β) [Finite V(G)] [Finite E(G)] (hV : V(G).Nonempty) :
    ∃ v, G.degree v = Δ(G) := by
  unfold maxDegree
  obtain ⟨k, hk⟩ := Finset.max_of_nonempty (by simpa : (G.degree '' V(G)).toFinset.Nonempty)
  have := Finset.mem_of_max hk
  simp only [toFinset_image, Finset.mem_image, mem_toFinset] at this
  obtain ⟨v, hv, rfl⟩ := this
  use v
  simp only [hk, WithBot.unbotD_coe]

noncomputable def minDegree (G : Graph α β) [Finite V(G)] [Finite E(G)] : ℕ :=
  (G.degree '' V(G)).toFinset.min.untopD 0

scoped notation "δ(" G ")" => minDegree G

lemma minDegree_le_degree (G : Graph α β) [Finite V(G)] [Finite E(G)] (hv : v ∈ V(G)) :
    δ(G) ≤ G.degree v := by
  unfold minDegree
  have hmem : G.degree v ∈ (G.degree '' V(G)).toFinset := by
    simp
    use v
  obtain ⟨e, he⟩ := Finset.min_of_mem hmem
  rw [he, WithTop.untopD_coe]
  have := Finset.min_le hmem
  simp_all only [toFinset_image, Finset.mem_image, mem_toFinset, ENat.some_eq_coe, Nat.cast_le]

lemma exists_vertex_minDegree (G : Graph α β) [Finite V(G)] [Finite E(G)] (hV : V(G).Nonempty) :
    ∃ v, G.degree v = δ(G) := by
  unfold minDegree
  obtain ⟨k, hk⟩ := Finset.min_of_nonempty (by simpa : (G.degree '' V(G)).toFinset.Nonempty)
  have := Finset.mem_of_min hk
  simp only [toFinset_image, Finset.mem_image, mem_toFinset] at this
  obtain ⟨v, hv, rfl⟩ := this
  use v
  simp only [hk, WithTop.untopD_coe]

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

lemma not_isLink_left (hisol : G.Isolated u) : ¬ G.IsLink e u v :=
  (hisol e ·.inc_left)

lemma not_isLink_right (hisol : G.Isolated u) : ¬ G.IsLink e v u :=
  (hisol e ·.inc_right)

end Isolated

lemma isolated_of_E_empty (hE : E(G) = ∅) : G.Isolated u := by
  intro e hinc
  exact (hE ▸ hinc.edge_mem : e ∈ ∅)

lemma degree_eq_zero_iff_isolated (G : Graph α β) [Finite E(G)] (v : α) :
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

section parallel

def parallel (G : Graph α β) (e f : β) : Prop :=
  e ∈ E(G) ∧ f ∈ E(G) ∧ G.IsLink e = G.IsLink f

lemma parallel.left_mem (h : G.parallel e f) : e ∈ E(G) := h.1

lemma parallel.right_mem (h : G.parallel e f) : f ∈ E(G) := h.2.1

lemma parallel.isLink_eq (h : G.parallel e f) : G.IsLink e = G.IsLink f := h.2.2

@[simp]
lemma parallel_refl (he : e ∈ E(G)) : G.parallel e e := ⟨he, he, rfl⟩

lemma parallel_iff_sym2_eq (G : Graph α β) (e f : β) :
    G.parallel e f ↔ ∃ (he : e ∈ E(G)) (hf : f ∈ E(G)), G.toSym2 e he = G.toSym2 f hf := by
  refine ⟨fun ⟨he, hf, h⟩ ↦ ⟨he, hf, ?_⟩, fun ⟨he, hf, h⟩ ↦ ⟨he, hf, ?_⟩⟩
  · rwa [toSym2_eq_toSym2_iff]
  · rwa [toSym2_eq_toSym2_iff] at h

@[simp]
lemma toSym2_eq_toSym2_iff_parallel (G : Graph α β) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G)) :
    G.toSym2 e he = G.toSym2 f hf ↔ G.parallel e f := by
  simp [parallel_iff_sym2_eq, he, hf]

lemma parallel.toSym2_eq (h : G.parallel e f) : G.toSym2 e h.left_mem = G.toSym2 f h.right_mem := by
  obtain ⟨he, hf, h⟩ := G.parallel_iff_sym2_eq e f |>.mp h
  exact h

lemma parallel_iff_inc_eq (G : Graph α β) (e f : β) :
    G.parallel e f ↔ e ∈ E(G) ∧ f ∈ E(G) ∧ G.Inc e = G.Inc f := by
  refine ⟨fun ⟨he, hf, h⟩ ↦ ⟨he, hf, ?_⟩, fun ⟨he, hf, h⟩ ↦ ⟨he, hf, ?_⟩⟩
  · rwa [inc_eq_inc_iff]
  · rwa [inc_eq_inc_iff] at h

@[simp]
lemma inc_eq_inc_iff_parallel (G : Graph α β) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G)) :
    G.Inc e = G.Inc f ↔ G.parallel e f := by
  simp [parallel_iff_inc_eq, he, hf]

lemma parallel.inc_eq (h : G.parallel e f) : G.Inc e = G.Inc f := by
  obtain ⟨he, hf, h⟩ := G.parallel_iff_inc_eq e f |>.mp h
  exact h

end parallel

section edgeNeighborhood
def edgeNeighborhood (G : Graph α β) (v : α) := {e : β | G.Inc e v}

scoped notation "Nₑ(" G "," v ")" => edgeNeighborhood G v

@[simp]
lemma mem_edgeNeighborhood_iff (G : Graph α β) (v : α) (e : β) :
    e ∈ Nₑ(G, v) ↔ G.Inc e v := by simp [edgeNeighborhood]

lemma edgeNeighborhood_subset_edgeSet (G : Graph α β) (v : α) :
    Nₑ(G, v) ⊆ E(G) := fun _ hx => hx.edge_mem

instance edgeNeighborhood_finite (G : Graph α β) (v : α) [Finite E(G)] :
    Finite (Nₑ(G, v)) := Finite.Set.subset E(G) (G.edgeNeighborhood_subset_edgeSet v)

lemma edgeNeighborhood_ncard_le_degree (G : Graph α β) (v : α) [Finite E(G)] :
    Nₑ(G, v).ncard ≤ G.degree v := by
  rw [degree_eq_edgeSet_sum]
  rw [ncard_eq_toFinset_card Nₑ(G, v), Finset.card_eq_sum_ones]
  apply le_trans (Finset.sum_le_sum fun e he ↦ ?_) (Finset.sum_le_sum_of_subset ?_)
  · exact toFinset_subset_toFinset.mpr <| G.edgeNeighborhood_subset_edgeSet v
  · simp only [toFinite_toFinset, mem_toFinset, mem_edgeNeighborhood_iff] at he
    rw [← incFun_ne_zero] at he
    exact Nat.one_le_iff_ne_zero.mpr he

end edgeNeighborhood
section vertexNeighborhood

def vertexNeighborhood (G : Graph α β) (v : α) := {x : α | G.Adj v x}

scoped notation "N(" G "," v ")" => vertexNeighborhood G v

@[simp]
lemma mem_vertexNeighborhood_iff (G : Graph α β) (v : α) (x : α) :
    x ∈ N(G, v) ↔ G.Adj v x := by simp [vertexNeighborhood]

lemma mem_vertexNeighborhood_comm (G : Graph α β) (v w : α) :
    v ∈ N(G, w) ↔ w ∈ N(G, v) := by
  simp only [vertexNeighborhood, mem_setOf_eq]
  rw [adj_comm]

lemma vertexNeighborhood_subset_vertexSet (G : Graph α β) (v : α) :
    N(G, v) ⊆ V(G) := fun _ hx => hx.mem_right

instance vertexNeighborhood_finite (G : Graph α β) (v : α) [Finite V(G)] :
    Finite (N(G, v)) := Finite.Set.subset V(G) (G.vertexNeighborhood_subset_vertexSet v)

lemma vertexNeighborhood_empty_of_isolated (G : Graph α β) (v : α) (hiso : G.Isolated v) :
    N(G, v) = ∅ := by
  simp only [vertexNeighborhood, eq_empty_iff_forall_notMem]
  intro x hx
  exact hiso.not_adj_left hx

lemma vertexNeighborhood_ncard_le_edgeNeighborhood_ncard (G : Graph α β) [hβ : Nonempty β] (v : α)
    [Finite E(G)] : N(G, v).ncard ≤ Nₑ(G, v).ncard := by
  classical
  simp only [vertexNeighborhood, edgeNeighborhood]
  refine ncard_le_ncard_of_injOn (fun x ↦ if hadj : G.Adj v x then hadj.choose else hβ.some) ?_ ?_ ?_
  · intro x hadj
    simp only [mem_setOf_eq] at hadj
    simp only [hadj, ↓reduceDIte, mem_setOf_eq, hadj.choose_spec.inc_left]
  · intro x hadj1 y hadj2 heq
    simp only [mem_setOf_eq] at hadj1 hadj2
    simp [hadj1, hadj2] at heq
    have h1 := hadj1.choose_spec
    have h2 := heq ▸ hadj2.choose_spec
    rwa [h1.isLink_iff_eq_right] at h2
  · change Finite (Nₑ(G, v))
    exact Finite.Set.subset E(G) (G.edgeNeighborhood_subset_edgeSet v)

lemma vertexNeighborhood_ncard_le_degree (G : Graph α β) (v : α) [Nonempty β] [Finite E(G)] :
    N(G, v).ncard ≤ G.degree v :=
  (vertexNeighborhood_ncard_le_edgeNeighborhood_ncard G v).trans
  (G.edgeNeighborhood_ncard_le_degree v)



end vertexNeighborhood
end Graph
