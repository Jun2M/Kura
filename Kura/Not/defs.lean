import Mathlib.Tactic
import Kura.Dep.Sym2


-- Do I need a separate none (edge not bound) that is not dir (none × none)?
-- For now, dir (none × none) represents that the edge is not bound
inductive edge (V : Type*)
| dir : Option V × Option V → edge V
| undir : {a : Multiset V // Multiset.card a = 2} → edge V

-- @[match_pattern]
-- def edge.sym2 {V : Type*} : Sym2 V → edge V := (undir <| Sym2.equivMultiset V ·)

@[ext]
structure Graph (V : Type*) (E : Type*) [DecidableEq V] [DecidableEq E] where
  inc : E → edge V

namespace Graph
open edge
variable {V : Type*} {E : Type*} [DecidableEq V] [DecidableEq E] (G : Graph V E)

def boundE : Set E := {e : E | G.inc e ≠ dir (none, none)}

def start (e : E) : Multiset V :=
  match G.inc e with
  | undir ⟨m, _⟩ => m
  | dir (a, _) =>
    match a with
    | some a => {a}
    | none => ∅

def finish (e : E) : Multiset V :=
  match G.inc e with
  | undir ⟨m, _⟩ => m
  | dir (_, b) =>
    match b with
    | some b => {b}
    | none => ∅

def ends (e : E) : Multiset V := match G.inc e with
  | undir ⟨m, _h⟩ => m
  | dir (a, b) => [a, b].foldl (λ s x =>
    match x with
    | some x => insert x s
    | none => s) ∅

def passible (e : E) (u v : V) : Bool :=
  match G.inc e with
  | undir ⟨m, _⟩ => m = {u, v}
  | dir (some a, some b) => a = u ∧ b = v
  | _ => false

lemma mem_boundE_iff_ends_nonempty (e : E) : e ∈ G.boundE ↔ (G.ends e) ≠ ∅ := by
  unfold boundE ends
  match hag : G.inc e with
  | dir (a, b) => cases a <;> cases b <;> simp [hag]
  | undir ⟨m, hm⟩ =>
    simp only [ne_eq, Set.mem_setOf_eq, hag, not_false_eq_true, Multiset.empty_eq_zero, true_iff]
    apply_fun Multiset.card
    simp [hm]

/-- An edge is `full` if it actually has two ends -/
def full (e : E) : Bool := match G.inc e with
  | undir _ => true
  | dir (some _, some _) => true
  | _ => false

def free (e : E) : Bool := match G.inc e with
  | dir (none, none) => true
  | _ => false

def isDir (e : E) : Bool := match G.inc e with
  | dir _ => true
  | _ => false

def isUndir (e : E) : Bool := match G.inc e with
  | dir _ => false
  | _ => true

lemma full_of_undir (h : G.isUndir e) : G.full e := by
  unfold full isUndir at *
  match hag : G.inc e with
  | dir _ => simp [hag] at h
  | undir _ => simp

lemma dir_or_undir (e : E) : G.isDir e ∨ G.isUndir e := by
  unfold isDir isUndir
  cases G.inc e <;> simp

@[simp]
def loop (e : E) : Bool := match G.inc e with
  | dir (some a, some b) => a = b
  | undir ⟨m, _⟩ => ¬ m.Nodup
  | _ => false

@[simp]
def arc (e : E) : Bool := match G.inc e with
  | dir (some a, some b) => a ≠ b
  | _ => false

@[simp]
def halfEdge (e : E) : Bool := match G.inc e with
  | dir (some _, none) => true
  | dir (none, some _) => true
  | _ => false


def edge_between (e : E) (v₁ v₂ : V) : Prop :=
  G.inc e = undir ⟨{v₁, v₂}, Multiset.card_pair v₁ v₂⟩

/-- Two vertices are adjacent if there is an edge having both vertices as ends. -/
def adj (u v : V) : Prop := ∃ e, u ∈ G.ends e ∧ v ∈ G.ends e

/-- A full graph is one with no half-edges. Can have a free edge!-/
class fullGraph : Prop :=
  no_half : ∀ e, ¬ G.halfEdge e

/-- An undirected graph is a full graph with no arcs -/
class undirected extends fullGraph G :=
  edge_symm : ∀ e, G.isUndir e

/-- A loopless graph is one with no loops, free edges or half_edges
  (so every edge is an arc or edge ) -/
class loopless extends fullGraph G :=
  no_loops : ∀ e, ¬G.loop e

-- class multiGraph extends undirected G :=
-- (no_free : ∀ e, ¬G.free e)

/-- A simple graph is one where every edge is a actual undirected 'edge'
  and no two edges have the same ends.  -/
class simple extends loopless G, undirected G :=
  inc_inj : G.inc.Injective

def edge_set (G : Graph V (V × V)) : Set (V × V) := { e | G.edge_between e e.1 e.2 }


-- example graphs
@[simp]
def CompleteGraphN (n : Nat) : Graph (Fin n) (Fin (n.choose 2)) where
  inc e := edge.undir <| ((List.finRange n).sublistsLen 2).get (e.cast (by simp))

instance : simple (CompleteGraphN n) where
  no_half := fun e => by simp
  no_loops := fun e => by
    simp
    obtain h := (Sym.listCombinations 2 (List.finRange n))[e.val].coe_mk_eq.symm
    rw [h]
    simp




  edge_symm := by sorry
  inc_inj := by sorry

-- Path

def takeEdge (e : E) (u : V) : Option V := match G.inc e with
  | dir (some a, b) => if a = u then b else none
  | undir m =>
    let m' := (Sym2.equivMultiset V).symm m
    if h : u ∈ m'
    then @Sym2.Mem.other' V _ u m' h
    else none
  | _ => none

lemma takeEdge_eq_some_iff_passible (e : E) (u v : V) : G.takeEdge e u = some v ↔ G.passible e u v = true := by
  unfold takeEdge passible
  match G.inc e with
  | dir (a, b) => cases a <;> cases b <;> simp
  | undir m =>
    simp only [decide_eq_true_eq]
    have hm : m.val = {u, v} ↔ m = ⟨{u, v}, by rfl ⟩ := by
      convert Subtype.coe_inj
      rfl
    rw [hm]; clear hm
    by_cases h : u ∈ (Sym2.equivMultiset V).symm m
    · simp only [h, ↓reduceDIte, Option.some.injEq]
      constructor
      · -- 1.
        intro hother
        apply_fun (Sym2.equivMultiset V).symm
        rw [Sym2.equivMultisetsymmEq, ← hother, eq_comm]
        exact Sym2.other_spec' h
      · -- 2.
        intro huv
        subst m
        simp only [Sym2.equivMultisetsymmEq] at h ⊢
        exact Sym2.other'_eq_right u v
    · simp only [h, ↓reduceDIte, false_iff, ne_eq]
      contrapose! h
      subst m
      rw [Sym2.mem_equivMultisetsymm_mem]
      simp



-- Connectedness

structure dirPath where
  start : V
  tail : List E
  prop : (tail.foldl (λ (a : Option V) (p : E) => a >>= G.takeEdge p) (some start)).isSome

def dirPath.finish (p : dirPath G) : V :=
  (p.tail.foldl (λ (a : Option V) (p : E) => a >>= G.takeEdge p) (some p.start)).get p.prop



def conn (u v : V) : Prop :=
  ∃ p : dirPath G, p.start = u ∧ p.tail ≠ [] ∧ (p.tail.last).finish = v
