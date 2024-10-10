import Kura.Graph.Edges
import Kura.Dep.Finset


@[ext]
structure Graph (V E : Type*) [LinearOrder V] where
  inc : E → edge V

namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E) (e e' : E) (u v w : V)


/- Carry the defs from Edges to Graph -/
@[simp] abbrev isDir : Bool := (G.inc e).isDir
@[simp] abbrev isUndir : Bool := (G.inc e).isUndir
@[simp] abbrev isFull : Bool := (G.inc e).isFull
@[simp] abbrev isHalf : Bool := (G.inc e).isHalf
@[simp] abbrev isFree : Bool := (G.inc e).isFree
@[simp] abbrev isLoop : Bool := (G.inc e).isLoop
@[simp] abbrev isArc : Bool := (G.inc e).isArc
@[simp] abbrev endAt : Multiset V := (G.inc e).endAt
@[simp] abbrev startAt : Multiset V := (G.inc e).startAt
@[simp] abbrev finishAt : Multiset V := (G.inc e).finishAt
@[simp] abbrev gofrom? (v : V) (e : E): Option V := (G.inc e).gofrom? v
@[simp] abbrev goback? (v : V) (e : E) : Option V := (G.inc e).goback? v
@[simp] abbrev canGo (v : V) (e : E) (w : V) : Bool := (G.inc e).canGo v w
@[simp] abbrev flip : edge V := (G.inc e).flip
@[simp] abbrev any := (G.inc e).any
@[simp] abbrev all := (G.inc e).all
@[simp] abbrev map (f : V → W) : edge W := (G.inc e).map f
@[simp] abbrev pmap {P : V → Prop} (f : ∀ a, P a → W) (e : E) :
  (∀ v ∈ G.inc e, P v) → edge W := ((G.inc e).pmap f ·)

/-- A full graph is one with no half-edges.-/
class fullGraph : Prop :=
  all_full : ∀ e, G.isFull e

/-- An undirected graph is a full graph with no arcs -/
class Undirected extends fullGraph G :=
  edge_symm : ∀ e, G.isUndir e

/-- A loopless graph is one with no loops, free edges or half_edges
  (so every edge is an arc or edge ) -/
class loopless extends fullGraph G :=
  no_loops : ∀ e, ¬G.isLoop e

def no_loops [loopless G] : ∀ e, ¬G.isLoop e := loopless.no_loops

/-- A simple graph is one where every edge is a actual undirected 'edge'
  and no two edges have the same ends.  -/
class Simple extends loopless G, Undirected G :=
  inc_inj : G.inc.Injective

class Directed extends fullGraph G :=
  no_undir : ∀ e, ¬G.isUndir e


/- Basic functions -/
-- def split : Multiset (Option V × E × Option V) := match G.inc e with
--   | dir p => {(p.fst, e, p.snd)}
--   | undir s => {(some s.inf, e, some s.sup), (some s.sup, e, some s.inf)}

def incEV := λ e => {v | v ∈ G.inc e}
def incVE := λ v => {e | v ∈ G.startAt e}
def incVV := λ v => {u | ∃ e, u ≠ v ∧ u ∈ G.inc e ∧ v ∈ G.inc e}
def incEE := λ e => {e' | (e = e' ∧ G.isLoop e) ∨ (e ≠ e' ∧ G.startAt e ∩ G.finishAt e' ≠ ∅)}

lemma loop_mem_incEE (hloop : G.isLoop e) : e ∈ G.incEE e := by
  simp only [incEE, Set.mem_setOf_eq, true_and]
  exact Or.inl hloop

lemma ne_of_mem_incEE_of_notLoop (h : e' ∈ G.incEE e) (hloop : ¬G.isLoop e) : e ≠ e' := by
  rintro rfl
  simp only [incEE, isLoop, ne_eq, startAt, finishAt, Multiset.empty_eq_zero, Set.mem_setOf_eq,
    true_and, not_true_eq_false, false_and, or_false] at h
  exact hloop h

def adj : Prop := ∃ e, G.canGo u e v
def neighbourhood : Set V := {u | G.adj u v}

macro u:term "--" e:term "--" v:term : term => `(G.canGo $u $e $v)

variable (H : Graph W F)

structure Hom where
  fᵥ : V → W
  fₑ : E → F
  comm : ∀ e, H.inc (fₑ e) = G.map e fᵥ

notation:20 lhs:20 " ⊆ᵍ " rhs:20 => Nonempty (Hom lhs rhs)

structure Isom where
  toHom : Hom G H
  toInv : Hom H G
  left_cancelᵥ : ∀ v, toHom.fᵥ (toInv.fᵥ v) = v
  right_cancelᵥ : ∀ v, toInv.fᵥ (toHom.fᵥ v) = v
  left_cancelₑ : ∀ e, toHom.fₑ (toInv.fₑ e) = e
  right_cancelₑ : ∀ e, toInv.fₑ (toHom.fₑ e) = e

def Hom.inj (a : Hom G H) : Prop := a.fᵥ.Injective ∧ a.fₑ.Injective

def Hom.surj (a : Hom G H) : Prop := a.fᵥ.Surjective ∧ a.fₑ.Surjective


end Graph
