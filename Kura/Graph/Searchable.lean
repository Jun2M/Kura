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

omit [DecidableEq V] in
lemma mem_outEdges_iff_mem_get [Undirected G] [SearchableOut G] :
  e ∈ G.outEdges v ↔ v ∈ s(G.v1 e, G.v2 e) := by
  rw [mem_outEdges]
  simp only [startAt, inc_eq_undir_v12, undir_startAt, Sym2.toMultiset_eq, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton, Sym2.mem_iff]

def outNeighbors [SearchableOut G] : List V :=
  G.outEdges v |>.filterMap (G.gofrom? v ·)
def outDegree [SearchableOut G] : ℕ :=
  G.outEdges v |>.filterMap (G.gofrom? v ·) |>.count v

lemma adj_iff_exist_outEdge_canGo [DecidableEq V] [SearchableOut G] :
    G.adj u v ↔ ∃ e ∈ G.outEdges u, G.canGo u e v := by
  sorry

lemma mem_outNeighbors_iff_adj [SearchableOut G] :
    w ∈ G.outNeighbors v ↔ G.adj v w := by
  unfold outNeighbors adj
  simp only [gofrom?, List.mem_filterMap, mem_outEdges, startAt, Option.mem_def,
    decide_eq_true_eq]
  refine exists_congr (fun e => ?_)
  rw [and_iff_right_of_imp (mem_startAt_of_gofrom?_eq  _ _ _)]
  refine (gofrom?_iff_goback?_iff_canGo (G.inc e) v w).out 0 2

instance instCycleGraphSearchableOut (n : ℕ+) : SearchableOut (CycleGraph n) where
  outEdges v := (List.finRange n).filter (λ e => v ∈ (CycleGraph n).startAt e)
  mem_outEdges v e := by
    simp only [startAt, inc_eq_undir_v12, undir_startAt, Sym2.toMultiset_eq,
      Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, Bool.decide_or,
      List.mem_filter, List.mem_finRange, Bool.or_eq_true, decide_eq_true_eq, true_and]

namespace BFS
variable [SearchableOut G]

def l (queuef : List V × (V → Option V)) (h : queuef.1 ≠ []) :=
  let queue := queuef.1
  let f := queuef.2
  let v := queue.head h
  G.outNeighbors v |>.filter (f ·|>.isNone) |>.dedup

def step : List V × (V → Option V) → List V × (V → Option V)
| (queue, f) => if h : queue = [] then (queue, f) else
  let v := queue.head h
  let l' := l G (queue, f) h
  (queue.tail ++ l', fun x => if x ∈ l' then some v else f x)

@[simp]
lemma step_queue_length (queuef : List V × (V → Option V)) (h : queuef.1 ≠ []) :
  (step G queuef).1.length = queuef.1.length - 1 + (l G queuef h).length := by
  simp only [step, h, ↓reduceDIte, Prod.mk.eta, List.length_append, List.length_tail]

@[simp]
lemma step_eq_of_some {queuef : List V × (V → Option V)} {w : V} (hw : (queuef.2 w).isSome) :
  (step G queuef).2 w = queuef.2 w := by
  by_cases hl : queuef.1 = [] <;> simp only [step, hl, ↓reduceDIte, l, outNeighbors, gofrom?,
    List.mem_dedup, List.mem_filter, List.mem_filterMap, mem_outEdges, startAt,
    Option.isNone_iff_eq_none, ite_eq_right_iff, and_imp, forall_exists_index]
  rintro e _ _ hNone
  simp only [hNone, Option.isSome_none, Bool.false_eq_true] at hw

lemma mem_BFS_step_queue_of_adj {queuef : List V × (V → Option V)} {w : V}
  (hqueue : queuef.1 ≠ []) (hwadj : G.adj (queuef.1.head hqueue) w) (hwf : queuef.2 w = none):
  w ∈ (step G queuef).1 := by
  simp only [step, hqueue, ↓reduceDIte, l, List.mem_dedup, List.mem_filter,
    Option.isNone_iff_eq_none, List.mem_append, hwf, Option.isNone_none, and_true]
  refine Or.inr <| (mem_outNeighbors_iff_adj _ _ _).mpr hwadj

def nones [Fintype V] (queuef : List V × (V → Option V)) : Finset V :=
  Finset.univ.filter (fun x ↦ (queuef.2 x).isNone)

def measure [Fintype V] (queuef : List V × (V → Option V)) : ℕ :=
  (nones queuef).card + queuef.1.length

@[simp]
lemma List.toFinset_dedup [Fintype V] (l : List V) : l.dedup.toFinset = l.toFinset := by
  rw [List.toFinset_eq_iff_perm_dedup, List.dedup_idem]

lemma disjoint_nones_step_l [Fintype V] (queuef : List V × (V → Option V)) (h : queuef.1 ≠ []) :
  Disjoint (nones (step G queuef)) (l G queuef h).toFinset := by
  simp [nones, step, h, ↓reduceDIte, l, List.mem_dedup, List.mem_filter,
    Option.isNone_iff_eq_none]
  rw [Finset.disjoint_left]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, not_and]
  rintro x hx hx2 h
  simp only [hx2, h, and_self, ↓reduceIte, reduceCtorEq] at hx

lemma nones_step_disjUnion_l_eq_nones [Fintype V] (queuef : List V × (V → Option V))
  (h : queuef.1 ≠ []) :
  (nones (step G queuef)).disjUnion (l G queuef h).toFinset (disjoint_nones_step_l G queuef h) =
  nones queuef := by
  ext v
  by_cases hv : v ∈ G.outNeighbors (queuef.1.head h) ∧ queuef.2 v = none
  <;> simp only [nones, step, h, ↓reduceDIte, l, List.mem_dedup, List.mem_filter,
    Option.isNone_iff_eq_none, List.toFinset_dedup, List.toFinset_filter, Finset.disjUnion_eq_union,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, hv, and_self, ↓reduceIte, reduceCtorEq,
    and_false, List.mem_toFinset, or_true, or_false]

lemma measure_decreasing [Fintype V] (queuef : List V × (V → Option V)) (h : queuef.1 ≠ []) :
  measure (step G queuef) < measure queuef := by
  let l' := l G queuef h
  let A := nones (step G queuef)
  let B := nones queuef
  change A.card + (step G queuef).1.length < B.card + queuef.1.length
  rw [step_queue_length]
  have hqueueLenPos : 0 < queuef.1.length := List.length_pos.mpr h
  suffices A.card + (l G queuef h).length ≤ B.card by omega
  have hlLen : _ = l'.length := List.toFinset_card_of_nodup <| List.nodup_dedup _
  rw [← hlLen]; clear hlLen
  obtain this : A.disjUnion l'.toFinset (disjoint_nones_step_l G queuef h) = B :=
    nones_step_disjUnion_l_eq_nones G queuef h
  apply_fun Finset.card at this
  rw [Finset.card_disjUnion] at this
  rw [this]

def rec [Fintype V] [SearchableOut G] (queuef : List V × (V → Option V)) : V → Option V :=
  match queuef with
  | (queue, f) => if h : queue = [] then f else rec (step G (queue, f))
termination_by measure queuef
decreasing_by exact measure_decreasing G (queue, f) h

end BFS

def BFS [Fintype V] [SearchableOut G] (v : V) : V → Option V :=
  BFS.rec G ([v], (if · = v then some v else none))

lemma isSome_BFS_of_adj_of_isSome_BFS [Fintype V] [SearchableOut G] {u v w : V} (h : G.adj v w)
    (hv : (G.BFS u v).isSome) : (G.BFS u w).isSome := by
  unfold BFS at hv ⊢
  sorry

#eval (CycleGraph 8).BFS 0



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

instance instAdjDecidableOfSearchableOut [DecidableEq V] [SearchableOut G] :
    ∀ u, DecidablePred (G.adj u ·) := by
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
