import Mathlib.Tactic
import Kura.Dep.Sym2
-- import Kura.Dep.FinE
import Kura.Dep.Option


-- Do I need a separate none (edge not bound) that is not dir (none × none)?
-- For now, dir (none × none) represents that the edge is not bound
inductive edge (V : Type*) [DecidableEq V]
| dir : Option V × Option V → edge V
| undir : Sym2 V → edge V

-- def edge (V : Type*) [DecidableEq V] := Option V × Option V ⊕ Sym2 V

unsafe instance [Repr V] [DecidableEq V] : Repr (edge V) where
  reprPrec e _ := match e with
    | edge.dir (a, b) => repr a ++ "-→" ++ repr b
    | edge.undir s => repr s

namespace edge

variable {V : Type*} [DecidableEq V] (e : edge V)


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
def flip : edge V := match e with
  | dir (a, b) => dir (b, a)
  | s => s

variable {W : Type*} [DecidableEq W]

def map (f : V → W) : edge V → edge W
| dir (a, b) => dir (a.map f, b.map f)
| undir s => undir (s.map f)

end edge


-- inductive edgeSorted (V : Type*) (R : V → V → Prop) [DecidableEq V]
--   [DecidableRel R] [IsAntisymm V R] [IsTotal V R]
-- | dir : Option V × Option V → edgeSorted V R
-- | undir : {vs : V × V // R vs.1 vs.2} → edgeSorted V R

-- namespace edgeSorted
-- variable {V : Type*} {R : V → V → Prop} [DecidableEq V]
--   [DecidableRel R] [IsAntisymm V R] [IsTotal V R] (e : edgeSorted V R)

-- @[simp]
-- def isDir : Bool := match e with
--   | dir _ => true
--   | _ => false

-- @[simp]
-- def isUndir : Bool := match e with
--   | undir _ => true
--   | _ => false

-- @[simp]
-- def isFull : Bool := match e with
--   | dir (some _, some _) => true
--   | undir _ => true
--   | _ => false

-- @[simp]
-- def isHalf : Bool := match e with
--   | dir (some _, none) => true
--   | dir (none, some _) => true
--   | _ => false

-- @[simp]
-- def isFree : Bool := match e with
--   | dir (none, none) => true
--   | _ => false


-- @[simp]
-- def isLoop : Bool := match e with
--   | dir (some a, some b) => a = b
--   | undir s => s.val.fst = s.val.snd
--   | _ => false

-- @[simp]
-- def isArc : Bool := match e with
--   | dir (some a, some b) => a ≠ b
--   | _ => false

-- @[simp]
-- def endAt : Multiset V := match e with
--   | dir (a, b) => [a, b].foldl (λ s x =>
--     match x with
--     | some x => insert x s
--     | none => s) ∅
--   | undir s => [s.val.fst, s.val.snd].foldl (λ s x => insert x s) ∅

-- @[simp]
-- def startAt : Multiset V := match e with
--   | dir (a, _) =>
--     match a with
--     | some a => {a}
--     | none => ∅
--   | undir s => [s.val.fst].foldl (λ s x => insert x s) ∅

-- @[simp]
-- def finishAt : Multiset V := match e with
--   | dir (_, b) =>
--     match b with
--     | some b => {b}
--     | none => ∅
--   | undir s => [s.val.snd].foldl (λ s x => insert x s) ∅

-- @[simp]
-- def gofrom (v : V) : Option V := match e with
--   | dir (a, b) => if a = v then b else none
--   | undir s => if v = s.val.fst then some s.val.snd
--     else if v = s.val.snd then some s.val.fst
--     else none

-- @[simp]
-- def goback (v : V) : Option V := match e with
--   | dir (a, b) => if b = v then a else none
--   | undir s => if v = s.val.fst then some s.val.snd
--     else if v = s.val.snd then some s.val.fst
--     else none

-- @[simp]
-- def flip : edgeSorted V R := match e with
--   | dir (a, b) => dir (b, a)
--   | s => s

-- end edgeSorted
