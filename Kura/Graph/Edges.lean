import Mathlib.Tactic
import Kura.Dep.Sym2
import Kura.Dep.Finset


-- Do I need a separate none (edge not bound) that is not dir (none × none)?
-- For now, dir (none × none) represents that the edge is not bound
inductive edge (V : Type*) [LinearOrder V]
| dir : Option V × Option V → edge V
| undir : Sym2 V → edge V
deriving Inhabited

-- def edge (V : Type*) [DecidableEq V] := Option V × Option V ⊕ Sym2 V

unsafe instance [Repr V] [LinearOrder V] : Repr (edge V) where
  reprPrec e _ := match e with
    | edge.dir (a, b) => repr a ++ "-→" ++ repr b
    | edge.undir s => repr s

namespace edge

variable {V : Type*} [LinearOrder V] (e : edge V)

instance instNonempty [Nonempty V] : Nonempty (edge V) :=
  Nonempty.intro (undir s(Classical.ofNonempty, Classical.ofNonempty))

def isDir  : Bool := match e with
  | dir _ => true
  | _ => false

def isUndir : Bool := match e with
  | undir _ => true
  | _ => false

def isFull : Bool := match e with
  | dir (some _, some _) => true
  | undir _ => true
  | _ => false

def isHalf : Bool := match e with
  | dir (some _, none) => true
  | dir (none, some _) => true
  | _ => false

def isFree : Bool := match e with
  | dir (none, none) => true
  | _ => false

def isLoop : Bool := match e with
  | dir (some a, some b) => a = b
  | undir s => s.IsDiag
  | _ => false

def isArc : Bool := match e with
  | dir (some a, some b) => a ≠ b
  | _ => false

@[simp]
lemma isUndir_of_undir (s : Sym2 V) : isUndir (undir s) := by
  unfold isUndir
  rfl

@[simp]
lemma isDir_of_dir (a b : Option V) : isDir (dir (a, b)) := by
  unfold isDir
  rfl

@[simp]
lemma not_isUndir_of_dir (a b : Option V) : ¬ isUndir (dir (a, b)) := by
  unfold isUndir
  tauto

@[simp]
lemma not_isDir_of_undir (s : Sym2 V) : ¬ isDir (undir s) := by
  unfold isDir
  tauto

-- @[simp]
-- lemma dir_not_isLoop_none_none : ¬ isLoop (dir (none, none) : edge V) := by
--   unfold isLoop
--   tauto

-- @[simp]
-- lemma dir_not_isLoop_none_some (a : V) : ¬ isLoop (dir (none, some a) : edge V) := by
--   unfold isLoop
--   tauto

-- @[simp]
-- lemma dir_not_isLoop_some_none (a : V) : ¬ isLoop (dir (some a, none) : edge V) := by
--   unfold isLoop
--   tauto

@[simp]
lemma dir_isLoop_iff (a b : V) : isLoop (dir (some a, some b)) ↔ a = b := by
  simp only [isLoop, decide_eq_true_eq]

@[simp]
lemma undir_isLoop_iff (s : Sym2 V) : isLoop (undir s) ↔ s.IsDiag := by
  simp only [isLoop, decide_eq_true_eq]

@[simp]
lemma dir_isFull_iff (a b : Option V) : isFull (dir (a, b)) ↔ a.isSome ∧ b.isSome := by
  cases a <;> cases b <;> simp [isFull, Bool.false_eq_true, Option.isSome_some,
    Option.isSome_none, and_false]

@[simp]
lemma undir_isFull (s : Sym2 V) : isFull (undir s) := by
  unfold isFull
  rfl

lemma isFull_of_isLoop (hloop : e.isLoop) : e.isFull := by
  match e with
  | dir (some a, some b) =>
    rw [dir_isLoop_iff] at hloop
    subst hloop
    simp only [isFull]
  | undir s => exact undir_isFull s



def endAt : Multiset V := match e with
  | dir (a, b) => [b, a].foldl (λ s x =>
    match x with
    | some x => insert x s
    | none => s) ∅
  | undir s => s.toMultiset

@[simp]
lemma dir_endAt (a b : V) : (dir (some a, some b)).endAt = {a, b} := by
  simp only [endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero, List.foldl_cons,
    Multiset.cons_zero, List.foldl_nil]

@[simp]
lemma undir_endAt (s : Sym2 V) : (undir s).endAt = s.toMultiset := by rfl

instance instedgeMem : Membership V (edge V) where
  mem e v := v ∈ e.endAt

instance instMemDecPred : ∀ (u : V), Decidable (u ∈ e) := by
  cases e <;> simp only [instedgeMem] <;> infer_instance

lemma mem_toMultiset_of_undir (e : Sym2 V) (v : V) : v ∈ undir e ↔ v ∈ e.toMultiset := by
  simp only [instedgeMem, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero, List.foldl_cons,
    Multiset.cons_zero, List.foldl_nil, Sym2.mem_toMultiset_iff]

@[simp]
lemma mem_undir_iff (e : Sym2 V) (v : V) : v ∈ undir e ↔ v ∈ e := by
  simp only [instedgeMem, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero, List.foldl_cons,
    Multiset.cons_zero, List.foldl_nil, Sym2.mem_toMultiset_iff]

def startAt : Multiset V := match e with
  | dir (a, _) =>
    match a with
    | some a => {a}
    | none => ∅
  | undir s => s.toMultiset

@[simp]
lemma undir_startAt (s : Sym2 V) : (undir s).startAt = s.toMultiset := by rfl

@[simp]
lemma mem_startAt_undir (s : Sym2 V) (v : V) : v ∈ startAt (undir s) ↔ v ∈ s := by
  simp only [startAt, Sym2.mem_toMultiset_iff]

def finishAt : Multiset V := match e with
  | dir (_, b) =>
    match b with
    | some b => {b}
    | none => ∅
  | undir s => s.toMultiset

@[simp]
lemma undir_finishAt (s : Sym2 V) : (undir s).finishAt = s.toMultiset := by rfl

@[simp]
lemma mem_finishAt_undir (s : Sym2 V) (v : V) : v ∈ finishAt (undir s) ↔ v ∈ s := by
  simp only [finishAt, Sym2.mem_toMultiset_iff]

@[simp]
lemma startAt_finishAt_not_disjoint_of_isLoop (e : edge V) : e.isLoop → e.startAt ∩ e.finishAt ≠ ∅ := by
  intro hloop
  match e with
  | dir (some a, some b) =>
    rw [dir_isLoop_iff] at hloop
    subst hloop
    simp only [startAt, finishAt, Multiset.inter_self, Multiset.empty_eq_zero, ne_eq,
      Multiset.singleton_ne_zero, not_false_eq_true]
  | undir s =>
    simp only [startAt, finishAt, Multiset.inter_self, Multiset.empty_eq_zero, ne_eq, ←
      Multiset.card_eq_zero, Sym2.toMultiset_card, OfNat.ofNat_ne_zero, not_false_eq_true]


def gofrom? (v : V) : Option V := match e with
  | dir (a, b) => if a = v then b else none
  | undir s => if h : v ∈ s then (@Sym2.Mem.other' V _ v s h) else none

def goback? (v : V) : Option V := match e with
  | dir (a, b) => if b = v then a else none
  | undir s => if h : v ∈ s then (@Sym2.Mem.other' V _ v s h) else none

def canGo (v : V) (e : edge V) (w : V) : Bool := w ∈ e.gofrom? v

theorem gofrom?_iff_goback?_iff_canGo (u v : V) :
  List.TFAE [e.gofrom? u = some v, e.goback? v = some u, e.canGo u v] := by
  refine List.tfae_of_forall (e.gofrom? u = some v) _ (fun p hp => ?_)
  fin_cases hp
  · rfl
  · match e with
    | dir (a, b) =>
      cases a <;> simp_all [gofrom?, goback?]
      split <;> simp_all
    | undir s =>
      simp [Sym2.eq_swap, gofrom?, goback?]
  · match e with
    | dir (a, b) => cases a <;> cases b <;> simp_all [canGo]
    | undir s => simp [canGo]

lemma mem_startAt_of_canGo (v w : V) : e.canGo v w → v ∈ e.startAt := by
  intro h
  match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all [canGo, startAt, gofrom?]
  | undir s =>
    simp_all only [canGo, gofrom?, Option.mem_def, dite_some_none_eq_some, Sym2.exist_other'_eq,
      decide_eq_true_eq, undir_startAt, Sym2.toMultiset_eq, Multiset.insert_eq_cons,
      Multiset.mem_cons, Multiset.mem_singleton, true_or]

lemma mem_finishAt_of_canGo (v w : V) : e.canGo v w → w ∈ e.finishAt := by
  intro h
  match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all [canGo, finishAt, gofrom?]
  | undir s =>
    simp_all only [canGo, gofrom?, Option.mem_def, dite_some_none_eq_some, Sym2.exist_other'_eq,
      decide_eq_true_eq, undir_finishAt, Sym2.toMultiset_eq, Multiset.insert_eq_cons,
      Multiset.mem_cons, Multiset.mem_singleton, or_true]

lemma isLoop_of_canGo_self : (∃ u, e.canGo u u) → e.isLoop := by
  match e with
  | dir (a, b) =>
    rintro ⟨ u, hu ⟩
    simp only [canGo, gofrom?, Option.mem_def, decide_eq_true_eq] at hu
    cases a <;> cases b <;> simp_all [Option.some.injEq, ite_some_none_eq_some, dir_isLoop_iff]
  | undir s =>
    rintro ⟨ u, hu ⟩
    simp only [canGo, gofrom?, Option.mem_def, dite_some_none_eq_some, Sym2.exist_other'_eq,
      decide_eq_true_eq] at hu
    subst hu
    simp only [undir_isLoop_iff, Sym2.isDiag_iff_proj_eq]


lemma undir_gofrom?_comm (s : Sym2 V) (v w : V) :
    (undir s).gofrom? v = some w ↔ (undir s).gofrom? w = some v := by
  simp only [gofrom?, dite_some_none_eq_some, Sym2.exist_other'_eq]
  refine Eq.congr_right ?h
  exact Sym2.eq_swap

@[simp]
lemma dir_canGo (a b : V) : (dir (some a, some b)).canGo a b := by
  simp only [canGo, gofrom?, ↓reduceIte, Option.mem_def, decide_True]

@[simp]
lemma undir_canGo (a b : V) : (undir s(a, b)).canGo a b := by
  simp only [canGo, gofrom?, Option.mem_def, dite_some_none_eq_some, Sym2.exist_other'_eq,
    decide_eq_true_eq]

@[simp]
lemma undir_canGo_inf_sup (s : Sym2 V) : (undir s).canGo s.inf s.sup := by
  simp only [canGo, gofrom?, Option.mem_def, dite_some_none_eq_some, Sym2.exist_other'_eq,
    Sym2.inf_sup_eq_self, decide_True]


@[simp]
def flip : edge V := match e with
  | dir (a, b) => dir (b, a)
  | s => s

@[simp]
lemma flip_gofrom? : e.flip.gofrom? = e.goback? := by
  unfold flip goback? gofrom?
  rcases e <;> simp only

@[simp]
lemma flip_goback? : e.flip.goback? = e.gofrom? := by
  unfold flip goback? gofrom?
  rcases e <;> simp only

@[simp]
lemma canGo_flip (v w : V) : e.flip.canGo w v = e.canGo v w  := by
  unfold flip canGo
  match e with
  | dir (a,b) =>
    simp only [gofrom?, Option.mem_def, decide_eq_decide]
    cases a <;> cases b <;> simp only [ite_some_none_eq_some, Option.some.injEq, ite_self] <;> tauto
  | undir s =>
    simp only [Option.mem_def, decide_eq_decide]
    refine undir_gofrom?_comm s _ _


@[simp]
lemma flip_self (s : Sym2 V) : (undir s).flip = undir s := by
  simp only [flip]

def any (P : V → Bool) : Bool := match e with
  | dir (a, b) => a.any P || b.any P
  | undir s => s.any P

@[simp]
lemma any_iff (P : V → Bool) : e.any P ↔ (∃ v ∈ e, P v) := by match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all [instedgeMem, any, Or.comm, endAt]
  | undir s => simp only [any, instedgeMem, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
    List.foldl_cons, Multiset.cons_zero, List.foldl_nil, mem_undir_iff, Sym2.any_iff]

def all (P : V → Bool) : Bool := match e with
  | dir (a, b) => a.all P && b.all P
  | undir s => s.all P

@[simp]
lemma all_iff (P : V → Bool) : e.all P ↔ (∀ v ∈ e, P v) := by match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all [instedgeMem, all, And.comm, endAt]
  | undir s => simp only [all, instedgeMem, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
    List.foldl_cons, Multiset.cons_zero, List.foldl_nil, mem_undir_iff, Sym2.all_iff]

variable {W : Type*} [LinearOrder W]

def map (f : V → W) : edge V → edge W
| dir (a, b) => dir (a.map f, b.map f)
| undir s => undir (s.map f)

lemma mem_map_of_mem (f : V → W) (v : V) (e : edge V) : v ∈ e → f v ∈ e.map f := by
  intro h
  match e with
  | dir (a, b) =>
    cases a<;> cases b<;> simp_all [instedgeMem, map, endAt]
    exact h.imp (by rw [·]) (by rw [·])
  | undir s =>
    simp_all only [instedgeMem, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
      List.foldl_cons, Multiset.cons_zero, List.foldl_nil, Sym2.mem_toMultiset_iff, map,
      Sym2.mem_map]
    use v

lemma mem_map (f : V → W) (v : W) (e : edge V) (h : v ∈ e.map f): ∃ y ∈ e, f y = v := by
  match e with
  | dir (a, b) =>
    cases a<;> cases b<;> simp_all [instedgeMem, map, endAt]
    rcases h with rfl | rfl <;> simp
  | undir s =>
    simp_all only [instedgeMem, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
      List.foldl_cons, Multiset.cons_zero, List.foldl_nil, map, Sym2.mem_toMultiset_iff,
      Sym2.mem_map]

@[simp]
lemma mem_map_iff (f : V → W) (v : W) (e : edge V) : v ∈ e.map f ↔ ∃ y ∈ e, f y = v := by
  refine ⟨mem_map f v e, ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact mem_map_of_mem f y e hy

lemma mem_map_sat {P : W → Prop} (f : V → W) (hf : ∀ v, P (f v)) (v : W) (e : edge V)
  (h : v ∈ e.map f) : P v := by
  obtain ⟨y, _hymem, rfl⟩ := mem_map f v e h
  exact hf y

def pmap {P : V → Prop} (f : ∀ a, P a → W) (e : edge V) : (∀ v ∈ e, P v) → edge W := by
  intro H
  match e with
  | dir (a, b) =>
    refine dir (a.pmap f fun v h => H v (by cases b <;> simp_all [instedgeMem, endAt]),
      b.pmap f fun v h => H v (by cases a <;> simp_all [instedgeMem, endAt]))
  | undir s =>
    refine undir (s.pmap f fun v hv => H v ?_)
    simp_all [instedgeMem]



end edge

inductive fullEdge (V : Type*) [LinearOrder V]
| dir : V × V → fullEdge V
| undir : Sym2 V → fullEdge V

variable {V : Type*} [LinearOrder V]
namespace fullEdge

def v1 : fullEdge V → V
| dir (a, _) => a
| undir s => s.inf

def v2 : fullEdge V → V
| dir (_, b) => b
| undir s => s.sup

end fullEdge

namespace edge

def toFullEdge (e : edge V) (he : e.isFull) : fullEdge V :=
  match e, he with
  | edge.dir (some a, some b), _ => fullEdge.dir (a, b)
  | edge.undir s, _ => fullEdge.undir s

def v1 (e : edge V) (he : e.isFull) : V := (toFullEdge e he).v1
def v2 (e : edge V) (he : e.isFull) : V := (toFullEdge e he).v2

-- @[simp]
-- lemma edge.toFullEdge_eq_dir (a b : V) (he : (edge.dir (some a, some b)).isFull) :
--   edge.toFullEdge (edge.dir (some a, some b)) he = fullEdge.dir (a, b) := rfl

-- @[simp]
-- lemma edge.toFullEdge_eq_undir (s : Sym2 V) (he : (edge.undir s).isFull) :
--   edge.toFullEdge (edge.undir s) he = fullEdge.undir s := rfl

@[simp]
lemma dir_v1 (a b : V) (he : (dir (some a, some b)).isFull) :
  (toFullEdge (dir (some a, some b)) he).v1 = a := rfl

@[simp]
lemma undir_v1 (s : Sym2 V) (he : (undir s).isFull) :
  (toFullEdge (undir s) he).v1 = s.inf := rfl

@[simp]
lemma dir_v2 (a b : V) (he : (dir (some a, some b)).isFull) :
  (toFullEdge (dir (some a, some b)) he).v2 = b := rfl

@[simp]
lemma undir_v2 (s : Sym2 V) (he : (undir s).isFull) :
  (toFullEdge (undir s) he).v2 = s.sup := rfl

lemma canGo_v1_v2 (e : edge V) (he : e.isFull) : canGo (e.v1 he) e (e.v2 he) := by
  match e, he with
  | edge.dir (some a, some b), _ => simp only [v1, dir_v1, v2, dir_v2, dir_canGo]
  | edge.undir s, _ => simp [v1, v2]

@[simp]
lemma isLoop_iff_v1_eq_v2 (e : edge V) (he : e.isFull) : e.isLoop ↔ e.v1 he = e.v2 he := by
  match e, he with
  | edge.dir (some a, some b), _ => simp only [v1, dir_v1, v2, dir_v2, dir_isLoop_iff]
  | edge.undir s, _ => simp only [undir_isLoop_iff, Sym2.isDiag_iff_inf_eq_sup, v1, undir_v1, v2,
    undir_v2]

end edge
