import Mathlib.Tactic
import Kura.Dep.Sym2
-- import Kura.Dep.FinE
import Kura.Dep.Option


-- Do I need a separate none (edge not bound) that is not dir (none × none)?
-- For now, dir (none × none) represents that the edge is not bound
inductive edge (V : Type*) [DecidableEq V]
| dir : Option V × Option V → edge V
| undir : Sym2 V → edge V
deriving Inhabited

-- def edge (V : Type*) [DecidableEq V] := Option V × Option V ⊕ Sym2 V

unsafe instance [Repr V] [DecidableEq V] : Repr (edge V) where
  reprPrec e _ := match e with
    | edge.dir (a, b) => repr a ++ "-→" ++ repr b
    | edge.undir s => repr s

namespace edge

variable {V : Type*} [DecidableEq V] (e : edge V)

instance instNonempty [Nonempty V] : Nonempty (edge V) :=
  Nonempty.intro (undir s(Classical.ofNonempty, Classical.ofNonempty))

@[simp]
def isDir  : Bool := match e with
  | dir _ => true
  | _ => false

@[simp]
def isUndir : Bool := match e with
  | undir _ => true
  | _ => false

@[simp]
def isFull : Bool := match e with
  | dir (some _, some _) => true
  | undir _ => true
  | _ => false

@[simp]
def isHalf : Bool := match e with
  | dir (some _, none) => true
  | dir (none, some _) => true
  | _ => false

@[simp]
def isFree : Bool := match e with
  | dir (none, none) => true
  | _ => false

@[simp]
def isLoop : Bool := match e with
  | dir (some a, some b) => a = b
  | undir s => s.IsDiag
  | _ => false

@[simp]
def isArc : Bool := match e with
  | dir (some a, some b) => a ≠ b
  | _ => false


@[simp]
def endAt : Multiset V := match e with
  | dir (a, b) => [a, b].foldl (λ s x =>
    match x with
    | some x => insert x s
    | none => s) ∅
  | undir s => s.toMultiset

@[simp]
instance : Membership V (edge V) where
  mem e v := v ∈ e.endAt

lemma mem_toMultiset_of_undir (e : Sym2 V) (v : V) : v ∈ undir e ↔ v ∈ e.toMultiset := by simp


@[simp]
def startAt : Multiset V := match e with
  | dir (a, _) =>
    match a with
    | some a => {a}
    | none => ∅
  | undir s => s.toMultiset

@[simp]
def finishAt : Multiset V := match e with
  | dir (_, b) =>
    match b with
    | some b => {b}
    | none => ∅
  | undir s => s.toMultiset

@[simp]
def gofrom (v : V) : Multiset V := match e with
  | dir (a, b) => if v = a then ∅ else b.toMultiset
  | undir s => if h : v ∈ s then {Sym2.Mem.other' h} else ∅

@[simp]
def gofrom? (v : V) : Option V := match e with
  | dir (a, b) => if a = v then b else none
  | undir s => if h : v ∈ s then (@Sym2.Mem.other' V _ v s h) else none

@[simp]
def goback? (v : V) : Option V := match e with
  | dir (a, b) => if b = v then a else none
  | undir s => if h : v ∈ s then (@Sym2.Mem.other' V _ v s h) else none

@[simp]
def canGo (v w : V) : Bool := w ∈ e.gofrom? v

theorem gofrom?_iff_goback?_iff_canGo (u v : V) :
  List.TFAE [e.gofrom? u = some v, e.goback? v = some u, e.canGo u v] := by
  refine List.tfae_of_forall (e.gofrom? u = some v) _ (fun p hp => ?_)
  fin_cases hp
  · rfl
  · match e with
    | dir (a, b) =>
      cases a <;> simp_all
      split <;> simp_all
    | undir s =>
      simp [Sym2.eq_swap]
  · match e with
    | dir (a, b) => cases a <;> cases b <;> simp_all
    | undir s => simp


@[simp]
def flip : edge V := match e with
  | dir (a, b) => dir (b, a)
  | s => s

variable {W : Type*} [DecidableEq W]

@[simp]
def map (f : V → W) : edge V → edge W
| dir (a, b) => dir (a.map f, b.map f)
| undir s => undir (s.map f)

lemma mem_map_of_mem (f : V → W) (v : V) (e : edge V) : v ∈ e → f v ∈ e.map f := by
  intro h
  match e with
  | dir (a, b) =>
    cases a<;> cases b<;> simp_all
    exact h.imp (by rw [·]) (by rw [·])
  | undir s =>
    simp_all only [instMembership, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
      List.foldl_cons, Multiset.cons_zero, List.foldl_nil, Sym2.mem_toMultiset_iff, map,
      Sym2.mem_map]
    use v

lemma mem_map (f : V → W) (v : W) (e : edge V) (h : v ∈ e.map f): ∃ y ∈ e, f y = v := by
  match e with
  | dir (a, b) =>
    cases a<;> cases b<;> simp_all
    rcases h with rfl | rfl <;> simp
  | undir s =>
    simp_all only [instMembership, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
      List.foldl_cons, Multiset.cons_zero, List.foldl_nil, map, Sym2.mem_toMultiset_iff,
      Sym2.mem_map]

def pmap {P : V → Prop} (f : ∀ a, P a → W) (e : edge V) : (∀ v ∈ e, P v) → edge W := by
  intro H
  match e with
  | dir (a, b) =>
    refine dir (a.pmap f fun v h => H v (by cases b <;> simp_all),
      b.pmap f fun v h => H v (by cases a <;> simp_all))
  | undir s =>
    refine undir (s.pmap f fun v hv => H v ?_)
    simp_all


end edge
