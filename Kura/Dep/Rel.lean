import Mathlib.Order.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Quotient
import Mathlib.Order.Rel.GaloisConnection
import Mathlib.Order.Closure
import Mathlib.Combinatorics.SimpleGraph.Path


lemma Irreflexive.ne_of_rel {α : Type u} {r : α → α → Prop} (h : Irreflexive r) {x y : α}
    (hxy : r x y) : x ≠ y := by
  rintro rfl
  exact h x hxy

def List.extend? {α : Type*} (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
    Option (List α) :=
  match l with
  | [] => none
  | h :: _ => if r a h then some (a :: l) else none

namespace Relation

instance ReflGenDecidable {α : Type*} {r : α → α → Prop} [DecidableEq α] [DecidableRel r] :
    DecidableRel (ReflGen r) :=
  fun a b => decidable_of_iff' (b = a ∨ r a b) (Relation.reflGen_iff r a b)

def finsetChainLength_rev {α : Type*} [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    (a : α) : (n : ℕ) → Finset (List α)
  | 0 => { [a] }
  | n + 1 => Finset.univ.biUnion fun (w : α) =>
      (finsetChainLength_rev r a n).filterMap (fun l => l.extend? (fun a b => r b a) w) (by
      intro l1 l2 b hl1 hl2
      simp only [List.extend?, Option.mem_def] at hl1 hl2
      cases l1 <;> cases l2 <;> simp_all [Option.ite_none_right_eq_some, Option.some.injEq,
        List.cons.injEq]
      obtain ⟨hl1head, hl1tail⟩ := hl1
      obtain ⟨hl2head, hl2tail⟩ := hl2
      subst hl2tail
      simpa using hl1tail)

def finsetChainLength {α : Type*} [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    (a : α) (n : ℕ) : Finset (List α) :=
  (finsetChainLength_rev r a n).map (⟨(·.reverse), fun _ _ => List.reverse_inj.mp⟩)

lemma mem_finsetChainLength_ne_nil {α : Type*} [Fintype α] [DecidableEq α] {r : α → α → Prop}
    [DecidableRel r] {a : α} {n : ℕ} {l : List α} (hl : l ∈ finsetChainLength r a n) : l ≠ [] := by
  match n with
  | 0 =>
    simp only [finsetChainLength, finsetChainLength_rev, Finset.map_singleton,
      Function.Embedding.coeFn_mk, List.reverse_cons, List.reverse_nil, List.nil_append,
      Finset.mem_singleton] at hl
    subst hl
    simp only [ne_eq, List.cons_ne_self, not_false_eq_true]
  | n + 1 =>
    simp only [finsetChainLength, finsetChainLength_rev, Finset.mem_map, Finset.mem_biUnion,
      Finset.mem_univ, Finset.mem_filterMap, true_and, Function.Embedding.coeFn_mk] at hl
    obtain ⟨b, ⟨⟨c, l', hl1, hl2⟩, rfl⟩⟩ := hl
    cases l' <;> simp [List.extend?, Option.mem_def] at hl2
    obtain ⟨d, rfl⟩ := hl2
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, ne_eq,
      List.append_eq_nil, List.reverse_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true]

lemma finsetChainLength_Chain' {α : Type*} [Fintype α] [DecidableEq α] {r : α → α → Prop}
    [DecidableRel r] {a : α} {n : ℕ} {l : List α} (hl : l ∈ finsetChainLength r a n) :
    l.Chain' r := by
  induction n generalizing l with
  | zero =>
    simp only [finsetChainLength, finsetChainLength_rev, Finset.map_singleton,
      Function.Embedding.coeFn_mk, List.reverse_cons, List.reverse_nil, List.nil_append,
      Finset.mem_singleton] at hl
    subst hl
    exact List.chain'_singleton _
  | succ n ih =>
    simp only [finsetChainLength, finsetChainLength_rev, Finset.mem_map, Finset.mem_biUnion,
      Finset.mem_univ, Finset.mem_filterMap, true_and, Function.Embedding.coeFn_mk,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hl ih
    obtain ⟨b, ⟨⟨c, l', hl1, hl2⟩, rfl⟩⟩ := hl
    cases' l' with a tl <;> simp [List.extend?, Option.mem_def] at hl2
    obtain ⟨d, rfl⟩ := hl2
    specialize ih _ hl1
    simp_all only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.chain'_append_cons_cons, List.chain'_singleton, and_self]

lemma ReflTransGen_iff_exists_finsetChainLength {α : Type*} [Fintype α] [DecidableEq α]
    {r : α → α → Prop} [DecidableRel r] {a b : α} : ReflTransGen r a b ↔
    ∃ (n : Fin (Fintype.card α)) (l : List α) (h : l ∈ finsetChainLength r a n),
    l.getLast (mem_finsetChainLength_ne_nil h) = b := by
  constructor
  · intro h
    obtain ⟨l, hlChain, hlLast⟩ := List.exists_chain_of_relationReflTransGen h
    rw [← hlLast]
    use sorry, l, sorry
    rw [List.getLast_cons]
  · rintro ⟨n, l, hl, rfl⟩
    have : l.head (mem_finsetChainLength_ne_nil hl) = a := by sorry
    apply l.tail.relationReflTransGen_of_exists_chain
    have hlChain := finsetChainLength_Chain' hl
    cases' l with hd tl
    · simp only [List.tail_nil, List.Chain.nil]
    · simp at this
      subst hd
      simp_all [List.Chain']
    congr
    rw [← this]
    simp only [List.head_cons_tail]

instance ReflTransGenDeciable {α : Type*} {r : α → α → Prop} [hFin: Fintype α] [hEq: DecidableEq α]
    [hRel : DecidableRel r] : DecidableRel (ReflTransGen r) := fun a b => by
  apply decidable_of_iff' _ (ReflTransGen_iff_exists_finsetChainLength)

def ReflClosure {α : Type*} : ClosureOperator (α → α → Prop) where
  toFun := ReflGen
  monotone' _ _ h _ _ h' := ReflGen.mono h h'
  le_closure' _ _ _ := ReflGen.single
  idempotent' _ := by
    ext a b
    constructor <;> rintro (h' | h')
    · exact ReflGen.refl
    · exact h'
    · exact ReflGen.refl
    · exact ReflGen.single (ReflGen.single h')

def TransClosure {α : Type*} : ClosureOperator (α → α → Prop) where
  toFun := TransGen
  monotone' _ _ h _ _ h' := TransGen.mono h h'
  le_closure' _ _ _ := TransGen.single
  idempotent' _ := by
    ext a b
    constructor <;> intro h
    · induction h with
      | single h => exact h
      | tail _ h' ih => exact TransGen.trans ih h'
    · exact TransGen.single h

def ReflTransClosure {α : Type*} : ClosureOperator (α → α → Prop) where
  toFun := ReflTransGen
  monotone' _ _ h _ _ h' := ReflTransGen.mono h h'
  le_closure' _ _ _ := ReflTransGen.single
  idempotent' _ := by
    ext a b
    constructor <;> intro h
    · induction h with
      | refl => exact ReflTransGen.refl
      | tail _ h' ih => exact ReflTransGen.trans ih h'
    · exact ReflTransGen.single h

def EqvGenClosure {α : Type*} : ClosureOperator (α → α → Prop) where
  toFun := EqvGen
  monotone' _ _ h _ _ h' := EqvGen.mono h h'
  le_closure' _ a b := EqvGen.rel a b
  idempotent' _ := by
    ext a b
    constructor <;> intro h
    · induction h with
      | rel _ _ h => exact h
      | refl => exact EqvGen.refl _
      | symm x y _ ih => exact EqvGen.symm x y ih
      | trans x y z _ _ ihxy ihyz => exact EqvGen.trans x y z ihxy ihyz
    · exact EqvGen.rel a b h

end Relation

namespace ClosureOperator

lemma closure_eq_closure_of_le_of_le_closure {α : Type*} {r s : α} [PartialOrder α]
  {c : ClosureOperator α} (hle : r ≤ s) (hlec : s ≤ c r) : c r = c s := by
  apply le_antisymm
  · exact c.monotone hle
  · exact le_closure_iff.mp hlec

end ClosureOperator
