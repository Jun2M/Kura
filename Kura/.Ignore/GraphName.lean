import Mathlib.Tactic
import Kuratowski.Dep.Sym2

open Set

/-- This is a weird, very 'inclusive' definition of a graph, allowing for directed/undirected edges
  and some more degenerate flavours of edge. Here, `inc false e` is the set of 'heads' of `e` and
  `inc true e` is the set of `tails`. The `well_def` axiom implies that both these sets have size at
  most two, and that if one has size two, they are the same set. This allows for 'free' edges with
  no ends, 'half-edges' with exactly one end (either the head or the tail), 'loops' with a head and
  a tail that are equal, 'arcs' with a head and tail that are distinct, and 'edges' with two heads
  and two tails so that the heads and the tails coincide. These can be thought of as edges directed
  in both ways, or equivalently as edges directed in neither way.

  The appearance of edges of all five types can be easily controlled using (data-free) typeclasses.
  This is really nice; it allows both digraphs and undirected graphs to be examples, without
  quotients.

  Half edges and free edges do appear in some mathematical contexts, and can be easily forbidden
  via typeclasses in contexts where they don't make sense. If we just forbid them, we basically
  get digraphs (where edges can be directed both ways at once).

  If arcs, half-edges and free edges are forbidden, then we get undirected multigraphs with loops.

  If, on top of this, we forbid loops and insist that the 'ends' map is injective, we get simple
  graphs.
  -/
@[ext]
structure Graph (V : Type*) (E : Type*) [DecidableEq V] [DecidableEq E] where
  inc : Bool → E → Finset V
  well_def : ∀ (i : Bool) (e : E), 2 ≤ (inc i e).card →
    ∃ (u v : V), u ≠ v ∧ ∀ j, inc j e = ({u, v} : Finset V)

structure Graphs (V : Type*) (E : Type*) [DecidableEq V] [DecidableEq E] where
  Vset : Set V
  Eset : Set E
  inc : Bool → E → Finset V
  edgeEnds : ∀ (i : Bool) (e : E), (inc i e) ⊆ setV
  well_def : ∀ (i : Bool) (e : E), 2 ≤ (inc i e).card →
    ∃ (u v : V), u ≠ v ∧ ∀ j, inc j e = ({u,v} : Set V)

-- inductive _Edge (V : Type*) where
--   | introUndirected (e : Sym2 V)
--   | introDirected (e : (Option V) × (Option V))

-- structure GraphCases (V : Type*) (E : Type*) where
--   inc : E → _Edge V

-- structure GraphCasesVsetEset where
--   Vset : Set V
--   Eset : Set E
--   inc : E → _Edge V
--   edgeEnds : ∀ (e : E),
--     match inc e with
--     | _Edge.introUndirected e => (↑e : Set V) ⊆ setV
--     | _Edge.introDirected (some v1, some v2) => v1 ∈ setV ∧ v2 ∈ setV
--     | _Edge.introDirected (some v1, none) => v1 ∈ setV
--     | _Edge.introDirected (none, some v2) => v2 ∈ setV
--     | _Edge.introDirected (none, none) => True


namespace Graph

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def mk' (inc : Bool → E → Finset V)
  (well_def' : ∀ (i : Bool) (e : E), (inc i e).card < 2 ∨ ((inc i e).card = 2 ∧ inc i e = inc (!i) e)) :
  Graph V E where
  inc := inc
  well_def := by
    intro i e heCard
    obtain (h1 | ⟨ hCard, hEq ⟩) := well_def' i e
    · exfalso
      exact not_lt_of_le heCard h1
    · obtain ⟨ u, v, huNeqv, hincEq ⟩ := Finset.card_eq_two.mp hCard
      refine ⟨ u, v, huNeqv, fun j => ?_ ⟩
      obtain (rfl | rfl) := j.eq_or_eq_not i
      · rw [hincEq]
      · rw [← hEq, hincEq]
    done

/-- An edge is `full` if it actually has two ends -/
def is_full (G : Graph V E) (e : E) : Prop := ∀ i, (G.inc i e).Nonempty

def ends (G : Graph V E) (e : E) : Finset V := G.inc false e ∪ G.inc true e

/-- `e: E` is undirected if all its end sets are the same -/
def undir (G : Graph V E) (e : E) : Prop := ∃ S : Finset V, ∀ i, G.inc i e = S

def free (G : Graph V E) (e : E) : Prop := ∀ i, G.inc i e = ∅

/-- `e : E` is a loop if all its end sets are the same singleton set -/
def loop (G : Graph V E) (e : E) : Prop := ∃ u, ∀ i, G.inc i e = {u}

/-- `e : E` is an edge if all its end sets are the same pair set -/
def edge (G : Graph V E) (e : E) : Prop := ∃ u v, u ≠ v ∧ ∀ i, G.inc i e = {u,v}

/-- `e : E` is an arc if it points from one vertex to another -/
def arc (G : Graph V E) (e : E) : Prop := ∃ u v, u ≠ v ∧ G.inc false e = {u} ∧ G.inc true e = {v}

def half_edge (G : Graph V E) (e : E) : Prop := ∃ i u, G.inc i e = {u} ∧ G.inc (!i) e = ∅

lemma inc_card_le (G : Graph V E) (i : Bool) (e : E) :
  (G.inc i e).card ≤ 2 := by
  by_contra! h
  obtain ⟨u,v,huv,h'⟩ := G.well_def i e h.le
  rw [h'] at h
  simpa using h.trans_le (Finset.card_insert_le _ _)
  done

lemma ends_card_le (G : Graph V E) (e : E) : (G.ends e).card ≤ 2 := by
  by_contra! h
  rw [Graph.ends] at h
  have : ∃ i, 2 ≤ (G.inc i e).card := by
    by_contra! h'
    simp_rw [Nat.lt_succ_iff] at h'
    linarith [h' true, h' false, h.trans_le (Finset.card_union_le _ _)]
  obtain ⟨i, hi⟩ := this
  obtain ⟨u, v, huv, h''⟩ := G.well_def i e hi
  rw [h'' true, h'' false, Finset.union_idempotent] at h
  simpa using h.trans_le (Finset.card_insert_le _ _)

-- lemma Finset.card_le_two {α : Type*} {s : Finset α} (hs : s.card ≤ 2) :
--   s = ∅ ∨ (∃ u, s = {u}) ∨ ∃ u v, u ≠ v ∧ s = {u,v} := by
--   rwa [le_iff_lt_or_eq, Finset.card_eq_two, Nat.lt_succ_iff_lt_or_eq, Nat.lt_succ_iff,
--     le_zero_iff, Finset.card_eq_zero, Finset.card_eq_one, or_assoc] at hs

-- lemma Finset.card_pair {α : Type*} {u v : α} (huv : u ≠ v) : ({u,v} : Finset α).card = 2 :=
-- by { rw [Finset.card_insert_eq_ite, if_neg, Finset.card_singleton]; rwa [Finset.mem_singleton] }

variable {G : Graph V E}

lemma edge_of_inc_card_eq_two {i : Bool} (h : (G.inc i e).card = 2) : G.edge e :=
by { have h' := G.well_def i e; rwa [h, imp_iff_right rfl.le] at h' }

lemma edge_iff_exists_inc_card_eq_two : G.edge e ↔ ∃ i, (G.inc i e).card = 2 := by
  refine ⟨λ h ↦ ⟨ true, ?_ ⟩, λ h => Exists.elim h (λ i => edge_of_inc_card_eq_two)⟩
  obtain ⟨u,v,huv,h⟩ := h
  rw [h, Finset.card_pair huv]

lemma free_or_half_edge_of_inc_eq_empty {i : Bool} (h : G.inc i e = ∅) : G.free e ∨ G.half_edge e := by
  obtain (h0 | h1) := eq_or_ne (G.inc (!i) e) ∅
  · left
    obtain (_ | _) := i <;> rintro (j | j) <;> assumption
  rw [←Finset.nonempty_iff_ne_empty, ←Finset.card_pos, ←Nat.succ_le_iff, le_iff_eq_or_lt,
    eq_comm, Finset.card_eq_one, Nat.lt_iff_add_one_le, (by rfl : (0:Nat).succ = 1), one_add_one_eq_two] at h1
  obtain (⟨a, ha⟩ | h2) := h1
  { right; use !i; use a; use ha; simpa }
  obtain ⟨ u, v, huv, h'⟩ := G.well_def (!i) e h2
  rw [h'] at h
  simp at h
  done

lemma arc_or_loop_or_half_edge_of_card_inc_eq_one {i : Bool} (h : (G.inc i e).card = 1) :
  G.arc e ∨ G.loop e ∨ G.half_edge e  := by
  rw [Finset.card_eq_one] at h
  obtain ⟨a, ha⟩ := h
  obtain (h0 | h1) := eq_or_ne (G.inc (!i) e) ∅
  { rcases (free_or_half_edge_of_inc_eq_empty h0).symm with h' | h'; right; right; assumption
    rw [h', eq_comm] at ha
    simp at ha }
  rw [←Finset.nonempty_iff_ne_empty, ←Finset.card_pos, ←Nat.succ_le_iff,
    le_iff_eq_or_lt, eq_comm, Finset.card_eq_one, Nat.lt_iff_add_one_le, (by rfl : (0:Nat).succ = 1), one_add_one_eq_two] at h1
  obtain (⟨b, hb⟩ | h2) := h1
  { obtain (rfl | hne) := eq_or_ne a b
    { right; left; use a; cases i<;> {rintro (j | j)<;> assumption } }
    left
    cases' i
    { exact ⟨ a, b, hne, ha, hb ⟩ }
    { exact ⟨ b, a, hne.symm, hb, ha ⟩ } }
  obtain ⟨u,v,huv, h⟩ := G.well_def _ _ h2
  apply_fun Finset.card at ha
  rw [h, Finset.card_pair huv, Finset.card_singleton] at ha
  simp at ha
  done

lemma edge_types (G : Graph V E) (e : E) :
  G.free e ∨ G.half_edge e ∨ G.loop e ∨ G.edge e ∨ G.arc e := by
  have h := G.inc_card_le true e
  obtain (h1 | h2) := lt_or_eq_of_le h
  { rw [Nat.lt_succ_iff, le_iff_eq_or_lt, Nat.lt_succ_iff,
      le_zero_iff, Finset.card_eq_zero] at h1
    cases' h1 with h1 h1
    { have := arc_or_loop_or_half_edge_of_card_inc_eq_one h1; tauto }
    have := free_or_half_edge_of_inc_eq_empty h1; tauto }
  have := edge_of_inc_card_eq_two h2; tauto

def edge_between (G : Graph V E) (e : E) (v₁ v₂ : V) : Prop := ∀ i, G.inc i e = {v₁,v₂}

/-- Two vertices are adjacent if there is an edge having both as ends. -/
def adj (G : Graph V E) (u v : V) : Prop := ∃ e, u ∈ G.ends e ∧ v ∈ G.ends e

/-- An undirected graph is one with no arcs or half-edges. -/
class undirected (G : Graph V E) : Prop := (edge_symm : ∀ e, G.undir e)

/-- A loopless graph is one with no loops, free edges or half_edges
  (so every edge is an arc or edge ) -/
class loopless (G : Graph V E) : Prop :=
(no_loops : ∀ e, ¬G.loop e)
(no_free : ∀ e, ¬G.free e)
(no_half : ∀ e, ¬G.half_edge e)

class multiGraph (G : Graph V E) extends undirected G :=
(no_free : ∀ e, ¬G.free e)

/-- A simple graph is one where every edge is a actual undirected 'edge'
  and no two edges have the same ends.  -/
class simple (G : Graph V E) extends loopless G, undirected G :=
(inc_inj : ∀ e f, (∀ i, G.inc i e = G.inc i f) → e = f)

def edge_set (G : Graph V (V × V)) : Set (V × V) := { e | G.edge_between e e.1 e.2 }

end Graph
