import Mathlib.Tactic
import Kura.Dep.Sym2
import Kura.Dep.Finset
import Kura.Dep.Option


open Sym2

-- Do I need a separate none (edge not bound) that is not dir (none × none)?
-- For now, dir (none × none) represents that the edge is not bound
inductive edge (V : Type*)
| dir : Option V × Option V → edge V
| undir : Sym2 V → edge V
deriving Inhabited

-- def edge (V : Type*) [DecidableEq V] := Option V × Option V ⊕ Sym2 V

unsafe instance [Repr V] : Repr (edge V) where
  reprPrec e _ := match e with
    | edge.dir (a, b) => repr a ++ "-→" ++ repr b
    | edge.undir s => repr s

namespace edge

variable {V : Type*} (e : edge V)

instance instNonempty [Nonempty V] : Nonempty (edge V) :=
  Nonempty.intro (undir s(Classical.ofNonempty, Classical.ofNonempty))

def isDir  : Prop := match e with
  | dir _ => true
  | _ => false

def isUndir : Prop := match e with
  | undir _ => true
  | _ => false

def isFull : Prop := match e with
  | dir (some _, some _) => true
  | undir _ => true
  | _ => false

def isHalf : Prop := match e with
  | dir (some _, none) => true
  | dir (none, some _) => true
  | _ => false

def isFree : Prop := match e with
  | dir (none, none) => true
  | _ => false

def isLoop : Prop := match e with
  | dir (some a, some b) => a = b
  | undir s => s.IsDiag
  | _ => false

def isArc : Prop := match e with
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
lemma not_isUndir_of_dir (x : Option V × Option V) : ¬ isUndir (dir x) := by
  unfold isUndir
  tauto

@[simp]
lemma not_isDir_of_undir (s : Sym2 V) : ¬ isDir (undir s) := by
  unfold isDir
  tauto

@[simp]
lemma not_isDir_iff_isUndir (e : edge V) : ¬ e.isDir ↔ e.isUndir := by
  cases e <;> simp only [isDir, isUndir] <;> tauto

@[simp]
lemma not_isUndir_iff_isDir (e : edge V) : ¬ e.isUndir ↔ e.isDir := by
  cases e <;> simp only [isDir, isUndir] <;> tauto

@[simp]
lemma exist_of_isDir (e : edge V) (he : e.isDir) : ∃ a b, e = dir (a, b) := by
  match e, he with
  | dir (a, b), _ => exact ⟨a, b, rfl⟩

@[simp]
lemma exist_of_isUndir (e : edge V) (he : e.isUndir) : ∃ s, e = undir s := by
  match e, he with
  | undir s, _ => exact ⟨s, rfl⟩

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

@[simp high]
lemma undir_isLoop_iff' (a b : V) : isLoop (undir s(a, b)) ↔ a = b := by
  rw [undir_isLoop_iff, isDiag_iff_proj_eq]

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

instance instMemDecPred [DecidableEq V] : ∀ (u : V), Decidable (u ∈ e) := by
  cases e <;> simp only [instedgeMem] <;> infer_instance

lemma mem_endAt_iff_mem (e : edge V) (v : V) : v ∈ e.endAt ↔ v ∈ e := by rfl

@[simp]
lemma mem_dir_some_fst (a : V) (b : Option V) : a ∈ dir (some a, b) := by
  simp only [instedgeMem, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero, List.foldl_cons,
    Multiset.cons_zero, List.foldl_nil, Multiset.mem_cons, true_or]

@[simp]
lemma mem_dir_some_snd (a : Option V) (b : V) : b ∈ dir (a, some b) := by
  cases a <;> simp only [instedgeMem, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
    List.foldl_cons, Multiset.cons_zero, List.foldl_nil, Multiset.mem_cons, Multiset.mem_singleton,
    or_true]

lemma mem_toMultiset_of_undir (e : Sym2 V) (v : V) : v ∈ undir e ↔ v ∈ e.toMultiset := by
  simp only [instedgeMem, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero, List.foldl_cons,
    Multiset.cons_zero, List.foldl_nil, mem_toMultiset_iff]

@[simp]
lemma mem_undir_iff (e : Sym2 V) (v : V) : v ∈ undir e ↔ v ∈ e := by
  simp only [instedgeMem, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero, List.foldl_cons,
    Multiset.cons_zero, List.foldl_nil, mem_toMultiset_iff]

def startAt : Multiset V := match e with
  | dir (a, _) =>
    match a with
    | some a => {a}
    | none => ∅
  | undir s => s.toMultiset

@[simp]
lemma dir_startAt (a b : Option V) :
    (dir (a, b)).startAt = if h : a.isSome then {a.get h} else ∅ := by
  cases a <;> simp only [startAt, Multiset.empty_eq_zero, Option.isSome_none, Bool.false_eq_true,
    ↓reduceDIte, Option.isSome_some, Option.get_some]

@[simp]
lemma undir_startAt (s : Sym2 V) : (undir s).startAt = s.toMultiset := by rfl

@[simp]
lemma mem_startAt_undir (s : Sym2 V) (v : V) : v ∈ startAt (undir s) ↔ v ∈ s := by
  simp only [startAt, mem_toMultiset_iff]

@[simp]
lemma undir_startAt_card (s : Sym2 V) : Multiset.card (undir s).startAt = 2 := by
  simp only [startAt, toMultiset_card]

lemma dir_startAt_card (x : Option V × Option V) : Multiset.card (dir x : edge V).startAt < 2 := by
  obtain ⟨a, b⟩ := x
  cases a <;> cases b <;> simp only [startAt, Multiset.empty_eq_zero, Multiset.card_zero,
    Nat.ofNat_pos, Multiset.card_singleton, Nat.one_lt_ofNat]

@[simp]
lemma dir_undir_startAt_not_eq (x : Option V × Option V) (s : Sym2 V) :
    (dir x).startAt ≠ (undir s).startAt := by
  apply_fun Multiset.card
  intro h
  rw [undir_startAt_card] at h
  exact (dir_startAt_card x).ne h

@[simp]
lemma startAt_subset_endAt (e : edge V) : e.startAt ⊆ e.endAt := by
  intro v hv
  match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all only [startAt, Multiset.mem_singleton, endAt,
      Multiset.insert_eq_cons, Multiset.empty_eq_zero, List.foldl_cons, Multiset.cons_zero,
      List.foldl_nil, Multiset.mem_cons, true_or, Multiset.not_mem_zero]
  | undir s =>
    simp_all only [undir_startAt, mem_toMultiset_iff, undir_endAt]

lemma mem_of_mem_startAt : ∀ v, v ∈ e.startAt → v ∈ e := by
  unfold instedgeMem
  exact startAt_subset_endAt e

def finishAt : Multiset V := match e with
  | dir (_, b) =>
    match b with
    | some b => {b}
    | none => ∅
  | undir s => s.toMultiset

@[simp]
lemma dir_finishAt (a b : Option V) :
    (dir (a, b)).finishAt = if h : b.isSome then {b.get h} else ∅ := by
  cases b <;> simp only [finishAt, Multiset.empty_eq_zero, Option.isSome_none, Bool.false_eq_true,
    ↓reduceDIte, Option.isSome_some, Option.get_some]

@[simp]
lemma undir_finishAt (s : Sym2 V) : (undir s).finishAt = s.toMultiset := by rfl

@[simp]
lemma mem_finishAt_undir (s : Sym2 V) (v : V) : v ∈ finishAt (undir s) ↔ v ∈ s := by
  simp only [finishAt, mem_toMultiset_iff]

@[simp]
lemma undir_finishAt_card (s : Sym2 V) : Multiset.card (undir s).finishAt = 2 := by
  simp only [finishAt, toMultiset_card]

@[simp]
lemma dir_finishAt_card (x : Option V × Option V) : Multiset.card (dir x : edge V).finishAt < 2 := by
  obtain ⟨a, b⟩ := x
  cases a <;> cases b <;> simp only [finishAt, Multiset.empty_eq_zero, Multiset.card_zero,
    Nat.ofNat_pos, Multiset.card_singleton, Nat.one_lt_ofNat]

@[simp]
lemma dir_undir_finishAt_not_eq (x : Option V × Option V) (s : Sym2 V) :
    (dir x).finishAt ≠ (undir s).finishAt := by
  apply_fun Multiset.card
  intro h
  rw [undir_finishAt_card] at h
  exact (dir_finishAt_card x).ne h

lemma finishAt_subset_endAt (e : edge V) : e.finishAt ⊆ e.endAt := by
  intro v hv
  match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all only [finishAt, Multiset.mem_singleton, endAt,
      Multiset.insert_eq_cons, Multiset.empty_eq_zero, List.foldl_cons, Multiset.cons_zero,
      List.foldl_nil, Multiset.mem_cons, or_true, Multiset.not_mem_zero]
  | undir s =>
    simp_all only [undir_finishAt, mem_toMultiset_iff, undir_endAt]

lemma mem_of_mem_finishAt : ∀ v, v ∈ e.finishAt → v ∈ e := by
  unfold instedgeMem
  exact finishAt_subset_endAt e

@[simp]
lemma startAt_finishAt_not_disjoint_of_isLoop [DecidableEq V] (e : edge V) :
    e.isLoop → e.startAt ∩ e.finishAt ≠ ∅ := by
  intro hloop
  match e with
  | dir (some a, some b) =>
    rw [dir_isLoop_iff] at hloop
    subst hloop
    simp only [startAt, finishAt, Multiset.inter_self, Multiset.empty_eq_zero, ne_eq,
      Multiset.singleton_ne_zero, not_false_eq_true]
  | undir s =>
    simp only [startAt, finishAt, Multiset.inter_self, Multiset.empty_eq_zero, ne_eq, ←
      Multiset.card_eq_zero, toMultiset_card, OfNat.ofNat_ne_zero, not_false_eq_true]

@[ext]
lemma ext (e e' : edge V) (hstart : e.startAt = e'.startAt) (hfin : e.finishAt = e'.finishAt) :
    e = e' := by
  match e, e' with
  | dir (a, b), dir (a', b') =>
    simp_all only [dir_startAt, Multiset.empty_eq_zero, dir_finishAt, dir.injEq, Prod.mk.injEq]
    cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all
  | undir s, undir s' =>
    simp_all only [undir_startAt, undir_finishAt, undir.injEq]
    ext v
    rw [← mem_toMultiset_iff, hstart, mem_toMultiset_iff]
  | dir (a, b), undir s =>
    exfalso
    apply dir_undir_finishAt_not_eq (a, b) s hfin
  | undir s, dir (a, b) =>
    exfalso
    apply dir_undir_finishAt_not_eq (a, b) s hfin.symm


def gofrom? [DecidableEq V] (v : V) : Option V := match e with
  | dir (a, b) => if a = v then b else none
  | undir s => if h : v ∈ s then (@Mem.other' V _ v s h) else none

def goback? [DecidableEq V] (v : V) : Option V := match e with
  | dir (a, b) => if b = v then a else none
  | undir s => if h : v ∈ s then (@Mem.other' V _ v s h) else none

def canGo [DecidableEq V] (v : V) (e : edge V) (w : V) : Bool := w ∈ e.gofrom? v

theorem gofrom?_iff_goback?_iff_canGo [DecidableEq V] (u v : V) :
  List.TFAE [e.gofrom? u = some v, e.goback? v = some u, e.canGo u v] := by
  refine List.tfae_of_forall (e.gofrom? u = some v) _ (fun p hp => ?_)
  fin_cases hp
  · rfl
  · match e with
    | dir (a, b) =>
      cases a <;> simp_all [gofrom?, goback?]
      split <;> simp_all
    | undir s =>
      simp [eq_swap, gofrom?, goback?]
  · match e with
    | dir (a, b) => cases a <;> cases b <;> simp_all [canGo]
    | undir s => simp [canGo]

lemma mem_startAt_of_canGo [DecidableEq V] (v w : V) : e.canGo v w → v ∈ e.startAt := by
  intro h
  match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all [canGo, startAt, gofrom?]
  | undir s =>
    simp_all only [canGo, gofrom?, Option.mem_def, dite_some_none_eq_some, exist_other'_eq,
      decide_eq_true_eq, undir_startAt, toMultiset_eq, Multiset.insert_eq_cons,
      Multiset.mem_cons, Multiset.mem_singleton, true_or]

lemma mem_finishAt_of_canGo [DecidableEq V] (v w : V) : e.canGo v w → w ∈ e.finishAt := by
  intro h
  match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all [canGo, finishAt, gofrom?]
  | undir s =>
    simp_all only [canGo, gofrom?, Option.mem_def, dite_some_none_eq_some, exist_other'_eq,
      decide_eq_true_eq, undir_finishAt, toMultiset_eq, Multiset.insert_eq_cons,
      Multiset.mem_cons, Multiset.mem_singleton, or_true]

lemma isLoop_of_canGo_self [DecidableEq V] : (∃ u, e.canGo u u) → e.isLoop := by
  match e with
  | dir (a, b) =>
    rintro ⟨ u, hu ⟩
    simp only [canGo, gofrom?, Option.mem_def, decide_eq_true_eq] at hu
    cases a <;> cases b <;> simp_all [Option.some.injEq, ite_some_none_eq_some, dir_isLoop_iff]
  | undir s =>
    rintro ⟨ u, hu ⟩
    simp only [canGo, gofrom?, Option.mem_def, dite_some_none_eq_some, exist_other'_eq,
      decide_eq_true_eq] at hu
    subst hu
    simp only [undir_isLoop_iff, isDiag_iff_proj_eq]


lemma undir_gofrom?_comm [DecidableEq V] (s : Sym2 V) (v w : V) :
    (undir s).gofrom? v = some w ↔ (undir s).gofrom? w = some v := by
  simp only [gofrom?, dite_some_none_eq_some, exist_other'_eq]
  refine Eq.congr_right ?h
  exact eq_swap

@[simp]
lemma dir_canGo [DecidableEq V] (a b : V) : (dir (some a, some b)).canGo a b := by
  simp only [canGo, gofrom?, ↓reduceIte, Option.mem_def, decide_True]

@[simp]
lemma undir_canGo [DecidableEq V] (a b : V) : (undir s(a, b)).canGo a b := by
  simp only [canGo, gofrom?, Option.mem_def, dite_some_none_eq_some, exist_other'_eq,
    decide_eq_true_eq]

@[simp]
lemma undir_canGo_inf_sup [DecidableEq V] (s : Sym2 V) : (undir s).canGo s.out.1 s.out.2 := by
  simp only [canGo, gofrom?, Option.mem_def, dite_some_none_eq_some, exist_other'_eq,
    Prod.mk.eta, Quot.out_eq, decide_True]


@[simp]
def flip : edge V := match e with
  | dir (a, b) => dir (b, a)
  | s => s

@[simp]
lemma flip_gofrom? [DecidableEq V] : e.flip.gofrom? = e.goback? := by
  unfold flip goback? gofrom?
  rcases e <;> simp only

@[simp]
lemma flip_goback? [DecidableEq V] : e.flip.goback? = e.gofrom? := by
  unfold flip goback? gofrom?
  rcases e <;> simp only

@[simp]
lemma canGo_flip [DecidableEq V] (v w : V) : e.flip.canGo w v = e.canGo v w  := by
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

variable {W U : Type*}

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
      List.foldl_cons, Multiset.cons_zero, List.foldl_nil, mem_toMultiset_iff, map,
      mem_map]
    use v

lemma mem_map (f : V → W) (v : W) (e : edge V) (h : v ∈ e.map f): ∃ y ∈ e, f y = v := by
  match e with
  | dir (a, b) =>
    cases a<;> cases b<;> simp_all [instedgeMem, map, endAt]
    rcases h with rfl | rfl <;> simp
  | undir s =>
    simp_all only [instedgeMem, endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
      List.foldl_cons, Multiset.cons_zero, List.foldl_nil, map, mem_toMultiset_iff,
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

@[simp]
lemma dir_iff_dir_of_map_eq (f : V → W) (s : edge V) (t : edge W) (hmap : s.map f = t) :
    s.isDir ↔ t.isDir  := by
  match s, t with
  | dir (a, b), dir (a', b') =>
    cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all [map]
  | undir s, undir t => simp_all [map]

@[simp]
lemma map_dir (f : V → W) (a b : Option V) : (dir (a, b)).map f = dir (a.map f, b.map f) := by
  simp only [map]

@[simp]
lemma map_undir (f : V → W) (s : Sym2 V) : (undir s).map f = undir (s.map f) := by
  simp only [map]

@[simp]
lemma map_eq_dir_map (f : V ↪ W) (a b : Option V) (s : edge V) :
    s.map f = dir (a.map f, b.map f) ↔ s = dir (a, b) := by
  constructor
  · intro h
    match s with
    | dir (a, b) =>
      cases a <;> cases b <;> simp [map_dir, Option.map_some', Option.map_none', dir.injEq,
        Prod.mk.injEq, Option.some_eq_map_iff, Option.none_eq_map_iff] at h ⊢ <;>
        exact ⟨h.1.symm, h.2.symm⟩
    | undir s =>
      exfalso
      have : (dir (a.map f, b.map f) : edge W).isDir := by rfl
      rw [← dir_iff_dir_of_map_eq f _ _ h] at this
      simp only [not_isDir_of_undir, Bool.false_eq_true] at this
  · rintro rfl
    simp only [map]

@[simp]
lemma map_eq_dir (f : V → W) (a b : Option W) (s : edge V) :
    s.map f = dir (a, b) ↔ ∃ a' b', s = dir (a', b') ∧ a'.map f = a ∧ b'.map f = b := by
  constructor
  · intro h
    match s with
    | dir (a, b) =>
      cases a <;> cases b <;> simp_all [map_dir, Option.map_some', Option.map_none', dir.injEq,
        Prod.mk.injEq, Option.some_eq_map_iff, Option.none_eq_map_iff] <;> obtain ⟨h1, h2⟩ := h <;>
        subst h1 h2 <;> simp
      · rename_i b
        use none, b
        simp only [and_self, Option.some.injEq, exists_eq_left']
      · rename_i a b
        use a, b
        simp only [and_self, Option.some.injEq, exists_eq_left']
    | undir s =>
      exfalso
      have : (dir (a, b) : edge W).isDir := by rfl
      rw [← dir_iff_dir_of_map_eq f _ _ h] at this
      simp only [not_isDir_of_undir, Bool.false_eq_true] at this
  · rintro ⟨a', b', rfl, rfl, rfl⟩
    simp only [map_dir]

@[simp]
lemma map_eq_undir (f : V → W) (e : edge V) (s : Sym2 W) :
    e.map f = undir s ↔ ∃ s', e = undir s' ∧ s'.map f = s := by
  cases e <;> simp_all [map, undir.injEq, exists_eq_left']


@[simp]
lemma map_startAt [DecidableEq W] (f : V → W) (e : edge V) :
    (e.map f).startAt = e.startAt.map f := by
  match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all [startAt, map, Multiset.map_cons, Multiset.map_zero]
  | undir s => simp only [map, undir_startAt, map_toMultiset]

@[simp]
lemma map_finishAt [DecidableEq W] (f : V → W) (e : edge V) :
    (e.map f).finishAt = e.finishAt.map f := by
  match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all [finishAt, map, Multiset.map_cons, Multiset.map_zero]
  | undir s => simp only [map, undir_finishAt, map_toMultiset]

@[simp]
lemma map_id : e.map id = e := by
  cases e <;> simp only [map, Option.map_id_fun, id_eq, Prod.mk.eta, map_id']

@[simp]
lemma map_comp (f : V → W) (g : W → U) (e : edge V) : e.map (g ∘ f) = (e.map f).map g := by
  cases e <;> simp only [map, Option.map_map, map_map]

@[simp]
lemma map_canGo [DecidableEq V] [DecidableEq W] (f : V ↪ W) (v w : V) :
    (e.map f).canGo (f v) (f w) ↔ e.canGo v w := by
  match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all [canGo, gofrom?, map, Option.map_none', Option.map_some',
      Option.mem_def, ite_some_none_eq_some, EmbeddingLike.apply_eq_iff_eq, Bool.decide_and,
      Bool.and_eq_true, decide_eq_true_eq, and_congr_left_iff]
  | undir s =>
    simp only [canGo, gofrom?, map_undir, Option.mem_def, dite_some_none_eq_some,
      exist_other'_eq, decide_eq_true_eq]
    constructor
    · rintro h
      ext x
      rw [eq_mk_out s, map_pair_eq, Sym2.ext_iff] at h
      specialize h (f x)
      rw [eq_mk_out s, mem_iff]
      simpa only [mem_iff, EmbeddingLike.apply_eq_iff_eq, Prod.mk.eta, Quot.out_eq] using h
    · rintro rfl
      simp only [map_pair_eq]


def pmap {P : V → Prop} (f : ∀ a, P a → W) (e : edge V) : (∀ v ∈ e, P v) → edge W := by
  intro H
  match e with
  | dir (a, b) =>
    refine dir (a.pmap f fun v h => H v (by cases b <;> simp_all [instedgeMem, endAt]),
      b.pmap f fun v h => H v (by cases a <;> simp_all [instedgeMem, endAt]))
  | undir s =>
    refine undir (s.pmap f fun v hv => H v ?_)
    simp_all [instedgeMem]

@[simp]
lemma pmap_dir {P : V → Prop} (f : ∀ a, P a → W) (a b : Option V) (h : ∀ v ∈ dir (a, b), P v) :
    (dir (a, b)).pmap f h = dir (a.pmap f fun v hv => (by simp_all only [Option.mem_def,
      mem_dir_some_fst]), b.pmap f fun v hv => (by simp_all only [Option.mem_def, mem_dir_some_snd])) := by
  simp only [pmap]

@[simp]
lemma pmap_undir {P : V → Prop} (f : ∀ a, P a → W) (s : Sym2 V) (h : ∀ v ∈ undir s, P v) :
    (undir s).pmap f h = undir (s.pmap f fun v hv => h v (by rwa [mem_undir_iff])) := by
  simp only [pmap]

@[simp]
lemma pmap_eq_dir {P : V → Prop} (e : edge V) (f : ∀ a, P a → W) (h : ∀ v ∈ e, P v) (a b : Option W) :
    e.pmap f h = dir (a, b) ↔ ∃ (a' b' : Option V) (hab' : e = dir (a', b')),
      a'.pmap f (λ v hv => h v (by simp_all only [Option.mem_def, mem_dir_some_fst])) = a ∧
      b'.pmap f (λ v hv => h v (by simp_all only [Option.mem_def, mem_dir_some_snd])) = b := by
  constructor
  · intro heq
    match e with
    | dir (a, b) =>
      cases a <;> cases b <;> simp_all only [pmap, dir.injEq, Prod.mk.injEq] <;>
        obtain ⟨h1, h2⟩ := heq <;> subst h1 h2
      · use none, none, ⟨rfl, rfl⟩
      · use none, some ‹V›, ⟨rfl, rfl⟩
      · use some ‹V›, none, ⟨rfl, rfl⟩
      · rename_i a b
        use some a, some b, ⟨rfl, rfl⟩
    | undir s => simp_all [pmap_undir, Option.pmap]
  · rintro ⟨a', b', rfl, rfl, rfl⟩
    simp only [pmap, Option.pmap]


@[simp]
lemma pmap_eq_undir_iff {P : V → Prop} (e : edge V) (f : ∀ a, P a → W) (h : ∀ v ∈ e, P v)
  (s : Sym2 W) : e.pmap f h = undir s ↔
    ∃ (s' : Sym2 _) (hs' : e = undir s'), s'.pmap f (λ v hv => (by simp_all)) = s := by
  simp only [pmap]
  split
  · simp only [Option.pmap, reduceCtorEq, IsEmpty.exists_iff, exists_false]
  · rename_i e he s hs
    simp_all only [undir.injEq]
    constructor
    · rintro rfl
      use s, rfl
    · rintro ⟨s', rfl, rfl⟩
      rfl

@[simp]
lemma pmap_subtype_map_val {P : V → Prop} (e : edge V) (h : ∀ v ∈ e, P v) :
    (e.pmap Subtype.mk h).map Subtype.val = e  := by
  match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all only [map, pmap, Option.pmap, Option.map_some',
      Option.map_none']
  | undir s => simp only [map, pmap, Sym2.pmap_subtype_map_val]

@[simp]
lemma pmap_startAt {P : V → Prop} (e : edge V) (f : ∀ a, P a → W) (h : ∀ v ∈ e, P v) :
    (e.pmap f h).startAt = e.startAt.pmap f (λ v hv => h v (mem_of_mem_startAt e v hv)) := by
  match e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all only [pmap, Option.pmap, dir_startAt, Option.isSome_some,
      Option.get_some, Multiset.empty_eq_zero, dite_eq_ite, ite_true] <;> rfl
  | undir s => simp only [startAt, pmap, pmap_toMultiset]

@[simp]
lemma pmap_finishAt {P : V → Prop} (e : edge V) (f : ∀ a, P a → W) (h : ∀ v ∈ e, P v) :
    (e.pmap f h).finishAt = e.finishAt.pmap f (λ v hv => h v (mem_of_mem_finishAt e v hv)) := by
  sorry


-- lemma pmap_id {P : V → Prop} (e : edge V) (h : ∀ v ∈ e, P v) : e.pmap (λ a _ => a) h = e := by
--   cases e <;> simp only [pmap, dir.injEq, undir.injEq]



end edge

inductive fullEdge (V : Type*)
| dir : V × V → fullEdge V
| undir : Sym2 V → fullEdge V

variable {V : Type*}
namespace fullEdge

noncomputable def v1 : fullEdge V → V
| dir (a, _) => a
| undir s => s.out.1

noncomputable def v2 : fullEdge V → V
| dir (_, b) => b
| undir s => s.out.2

end fullEdge

namespace edge

def toFullEdge (e : edge V) (he : e.isFull) : fullEdge V :=
  match e, he with
  | edge.dir (some a, some b), _ => fullEdge.dir (a, b)
  | edge.undir s, _ => fullEdge.undir s

noncomputable def v1 (e : edge V) (he : e.isFull) : V := (toFullEdge e he).v1
noncomputable def v2 (e : edge V) (he : e.isFull) : V := (toFullEdge e he).v2

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
lemma undir_v1 (s : Sym2 V) :
  (toFullEdge (undir s) (undir_isFull s)).v1 = s.out.1 := rfl

@[simp]
lemma dir_v2 (a b : V) (he : (dir (some a, some b)).isFull) :
  (toFullEdge (dir (some a, some b)) he).v2 = b := rfl

@[simp]
lemma undir_v2 (s : Sym2 V) :
  (toFullEdge (undir s) (undir_isFull s)).v2 = s.out.2 := rfl

@[simp]
lemma undir_v12_eq (s : Sym2 V) :
  undir s((toFullEdge (undir s) (undir_isFull s)).v1,
    (toFullEdge (undir s) (undir_isFull s)).v2) = undir s := by
  simp only [undir_v1, undir_v2, Prod.mk.eta, Quot.out_eq]

lemma canGo_v1_v2 [DecidableEq V] (e : edge V) (he : e.isFull) : canGo (e.v1 he) e (e.v2 he) := by
  match e, he with
  | edge.dir (some a, some b), _ => simp only [v1, dir_v1, v2, dir_v2, dir_canGo]
  | edge.undir s, _ => simp [v1, v2]

@[simp]
lemma isLoop_iff_v1_eq_v2 (e : edge V) (he : e.isFull) : e.isLoop ↔ e.v1 he = e.v2 he := by
  match e, he with
  | edge.dir (some a, some b), _ => simp only [v1, dir_v1, v2, dir_v2, dir_isLoop_iff]
  | edge.undir s, _ => simp only [undir_isLoop_iff, isDiag_iff_out_fst_eq_out_snd, v1, undir_v1, v2,
    undir_v2]

end edge
