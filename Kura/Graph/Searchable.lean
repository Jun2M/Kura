import Kura.Graph.Undirected
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.OpClass
import Kura.Examples.Defs


namespace Graph
open edge
variable {V W E F : Type*} (G : Graph V E) [DecidableEq V] (e : E) (u v w : V)


-- There is a finset of edges that leads out of a vertex
class SearchableOut where
  outEdges : V → List E
  mem_outEdges : ∀ v e, e ∈ outEdges v ↔ v ∈ G.startAt e


def outEdges [SearchableOut G] (v : V) : List E := SearchableOut.outEdges G v

omit [DecidableEq V] in
@[simp]
lemma mem_outEdges [SearchableOut G] : e ∈ G.outEdges v ↔ v ∈ G.startAt e := by
  rw [← SearchableOut.mem_outEdges (G := G) v e]
  rfl

def outNeighbors [SearchableOut G] : Multiset V :=
  G.outEdges v |>.map (G.endAt ·) |>.sum |>.filter (· ≠ v)
def outDegree [SearchableOut G] : ℕ :=
  G.outEdges v |>.map (G.endAt ·) |>.sum |>.count v

omit [DecidableEq V] in
lemma mem_outEdges_iff_mem_get [Undirected G] [SearchableOut G] :
  e ∈ G.outEdges v ↔ v ∈ s(G.v1 e, G.v2 e) := by
  rw [mem_outEdges]
  simp only [startAt, inc_eq_undir_v12, undir_startAt, Sym2.toMultiset_eq, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton, Sym2.mem_iff]

lemma adj_iff_exist_outEdge_canGo [DecidableEq V] [SearchableOut G] :
    G.adj u v ↔ ∃ e ∈ G.outEdges u, G.canGo u e v := by
  sorry

instance instCycleGraphSearchableOut (n : ℕ) (h : 1 < n) : SearchableOut (CycleGraph n h) where
  outEdges v := (List.finRange n).filter (λ e => v ∈ (CycleGraph n h).startAt e)
  mem_outEdges v e := by
    simp only [startAt, inc_eq_undir_v12, undir_startAt, Sym2.toMultiset_eq,
      Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, Bool.decide_or,
      List.mem_filter, List.mem_finRange, Bool.or_eq_true, decide_eq_true_eq, true_and]

def BFS_aux [Fintype V] [SearchableOut G] (queue : List V) (f : V → Option V) : V → Option V :=
  if h : queue = [] then f else
  let v := queue.head h
  let l := G.outEdges v |>.filterMap (G.gofrom? v ·) |>.filter (f ·|>.isNone) |>.dedup
  BFS_aux (queue.tail ++ l) (fun x => if x ∈ l then some v else f x)
termination_by (Finset.univ.filter (f ·|>.isNone)).card + queue.length
decreasing_by
  simp only [gofrom?, List.mem_dedup, List.mem_filter, List.mem_filterMap, mem_outEdges, startAt,
    Option.isNone_iff_eq_none, dite_eq_ite, List.length_append, List.length_tail, gt_iff_lt]
  let A := Finset.univ.filter (fun x ↦ (if x ∈ l then some v else f x) = none)
  let B := Finset.univ.filter (fun x ↦ f x = none)
  change A.card + (queue.length - 1 + l.length) < B.card + queue.length
  have hqueueLenPos : 0 < queue.length := List.length_pos.mpr h
  suffices A.card + l.length ≤ B.card by omega
  have hlLen : _ = l.length := List.toFinset_card_of_nodup <| List.nodup_dedup _
  have hlsuB : l.toFinset ⊆ B := fun x ↦ by
    simp only [gofrom?, List.mem_toFinset, List.mem_dedup, List.mem_filter, List.mem_filterMap,
      mem_outEdges, startAt, Option.isNone_iff_eq_none, Finset.mem_filter, Finset.mem_univ,
      true_and, and_imp, imp_self, implies_true, l, B]
  have : A ⊆ B \ l.toFinset := fun x ↦ by
    by_cases hx : x ∈ l <;> simp [Finset.mem_filter, Finset.mem_univ, hx, ↓reduceIte,
      reduceCtorEq, and_false, Finset.mem_sdiff, true_and, List.mem_toFinset, not_true_eq_false,
      imp_self, A, B]
  refine add_le_add_right (Finset.card_le_card this) _ |>.trans ?_
  rw [Finset.card_sdiff hlsuB, ← hlLen, Nat.sub_add_cancel (Finset.card_le_card hlsuB)]

lemma BFS_aux_monotone [Fintype V] [SearchableOut G] {v w : V} {f : V → Option V} (hf : (f w).isSome)
  (l : List V) : (G.BFS_aux l f w).isSome := by
  sorry

def BFS [Fintype V] [SearchableOut G] (v : V) : V → Option V :=
  BFS_aux G [v] (if · = v then some v else none)

lemma isSome_BFS_of_adj_of_isSome_BFS [Fintype V] [SearchableOut G] {u v w : V} (h : G.adj v w)
    (hv : (G.BFS u v).isSome) : (G.BFS u w).isSome := by
  unfold BFS at hv ⊢
  sorry

#eval (CycleGraph 8 (by omega)).BFS 0

-- There is a finset of edges that leads into a vertex
class SearchableIn where
  inEdges : V → List E
  mem_inEdges : ∀ v e, e ∈ inEdges v ↔ v ∈ G.finishAt e


def inEdges [SearchableIn G] (v : V) : List E := SearchableIn.inEdges G v

omit [DecidableEq V] in
@[simp]
lemma mem_inEdges [SearchableIn G] : e ∈ G.inEdges v ↔ v ∈ G.finishAt e := by
  rw [← SearchableIn.mem_inEdges (G := G) v e]
  rfl

def inNeighbors [SearchableIn G] : Multiset V :=
  G.inEdges v |>.map (G.endAt ·) |>.foldl (· + ·) ∅ |>.filter (· ≠ v)
def inDegree [SearchableIn G] : ℕ :=
  G.inEdges v |>.map (G.endAt ·) |>.foldl (· + ·) ∅ |>.count v


-- There is a finset of edges that are incident to a vertex
class Searchable extends SearchableOut G, SearchableIn G where

variable [Searchable G] [DecidableEq E]

def incEdges : List E := G.outEdges v ∪ G.inEdges v
def neighbors  : Multiset V :=
  G.incEdges v |>.map (G.endAt ·) |>.foldl (· + ·) ∅ |>.filter (· ≠ v)
def degree : ℕ :=
  G.incEdges v |>.map (G.endAt ·) |>.foldl (· + ·) ∅ |>.count v
-- Deliverately double counts loops

lemma incEdges_card_eq_degree [G.loopless] : (G.incEdges v).length = G.degree v := by
  sorry

@[simp]
lemma incEdges_eq_outEdges [G.Undirected] : G.incEdges v = G.outEdges v := by
  sorry

instance instAdjDecidable [DecidableEq V] [SearchableOut G] : ∀ u, DecidablePred (G.adj u ·) := by
  rintro u v
  apply decidable_of_iff _ (G.adj_iff_exist_outEdge_canGo u v).symm

def regular (k : ℕ) : Prop := ∀ v : V, G.degree v = k

instance instRegularDecidablePred : DecidablePred (G.regular ·) := by
  sorry

-- instance DecidableRelAdjOfFintypeE [Searchable G] : DecidableRel (G.adj : V → V → Prop) := by
--   intro u v
--   apply decidable_of_iff (G.outEdges u |>.filter (G.canGo u · v)).Nonempty
--   simp only [Finset.Nonempty, canGo, Finset.mem_filter, mem_outEdges, startAt, adj]
--   apply exists_congr
--   intro e
--   apply and_iff_right_of_imp
--   intro h
--   exact mem_startAt_of_canGo _ _ _ h


-- instance Searchable_of_FintypeE [DecidableEq V] [Fintype E] : Searchable G where
--   outEdges v := Fintype.elems.filter (λ e => v ∈ G.startAt e)
--   mem_outEdges v e := by
--     rw [Finset.mem_filter, and_iff_right_iff_imp]
--     exact fun _ => Fintype.complete e
--   inEdges v := Fintype.elems.filter (λ e => v ∈ G.finishAt e)
--   mem_inEdges v e := by
--     rw [Finset.mem_filter, and_iff_right_iff_imp]
--     exact fun _ => Fintype.complete e

def maxDegree [Fintype V] : ℕ := Finset.univ.image (G.degree ·) |>.max |>.getD 0
macro "Δ(" G:term ")" : term => `(Graph.maxDegree $G)

def maxDegreeVerts [Fintype V] : Finset V :=
  Finset.univ.filter (λ v => G.degree v = G.maxDegree)

@[simp]
lemma mem_maxDegreeVerts [Fintype V]  (v : V) :
    v ∈ G.maxDegreeVerts ↔ G.degree v = G.maxDegree := by
  simp only [maxDegreeVerts, Finset.mem_filter, Finset.mem_univ, true_and]

lemma maxDegreeVerts_nonempty [Fintype V]  (hΔ : Δ(G) ≠ 0) :
    G.maxDegreeVerts.Nonempty := by
  unfold Graph.maxDegreeVerts Finset.Nonempty maxDegree
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have : Finset.univ.image (G.degree ·) |>.Nonempty := sorry
  obtain ⟨ n, hn ⟩ := Finset.max_of_nonempty this
  obtain ⟨ x, _, hx ⟩ := Finset.exists_max_image Finset.univ (G.degree ·) sorry
  use x
  sorry

def minDegree [Fintype V] : ℕ := Finset.univ.image (G.degree ·) |>.min |>.getD 0
macro "δ(" G:term ")" : term => `(Graph.minDegree $G)

def minDegreeVerts [Fintype V] : Finset V :=
  Finset.univ.filter (λ v => G.degree v = G.minDegree)

@[simp]
lemma mem_minDegreeVerts [Fintype V]  (v : V) :
    v ∈ G.minDegreeVerts ↔ G.degree v = G.minDegree := by
  simp only [minDegreeVerts, Finset.mem_filter, Finset.mem_univ, true_and]

lemma minDegreeVerts_nonempty [Fintype V]  (hδ : δ(G) ≠ 0) :
    G.minDegreeVerts.Nonempty := by sorry

lemma minDegree_le_degree [Fintype V] (v : V) : δ(G) ≤ G.degree v := by
  sorry

lemma degree_le_maxDegree [Fintype V] (v : V) : G.degree v ≤ Δ(G) := by
  sorry



theorem handshake [Fintype V] [Fintype E] [Undirected G] :
    ∑ v, G.degree v = 2 * Fintype.card E := by
  sorry

lemma n_minDegree_le_two_m [Fintype V] [Fintype E] [Undirected G] :
    Fintype.card V * δ(G) ≤ 2 * Fintype.card E := by
  refine (?_ : _ ≤ _).trans G.handshake.le
  rw [← Finset.card_univ, ← Finset.sum_const_nat (?_ : ∀ v ∈ Finset.univ, (fun _ => δ(G)) v = δ(G))]
  apply Finset.sum_le_sum
  exact fun v _a ↦ minDegree_le_degree G v
  intro v _hv
  rfl
