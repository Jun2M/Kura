import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Quotient
import Mathlib.Order.Rel.GaloisConnection
import Mathlib.Order.Closure
import Mathlib.Combinatorics.SimpleGraph.Path
import Kura.Dep.List

variable {α : Type*} {r : α → α → Prop}


lemma Irreflexive.ne_of_rel (h : Irreflexive r) {x y : α}
    (hxy : r x y) : x ≠ y := by
  rintro rfl
  exact h x hxy

def List.extend? (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
    Option (List α) :=
  match l with
  | [] => none
  | h :: _ => if r a h then some (a :: l) else none

def List.Chain'_extend? (r : α → α → Prop) [DecidableRel r] (a : α)
    (l : {l : List α // l.Chain' r}) : Option {l : List α // l.Chain' r} :=
  match l with
  | ⟨[], _⟩ => none
  | ⟨b :: bs, hl⟩ => if hr : r a b then some ⟨a :: b :: bs, by simp only [chain'_cons, hr, hl,
    and_self]⟩ else none

variable [DecidableRel r]

lemma List.length_add_one_eq_of_Chain'_extend?_eq_some {a : α} {l l' : {l : List α // l.Chain' r}}
    (hl : List.Chain'_extend? r a l = some l') : l.val.length + 1 = l'.val.length := by
  unfold List.Chain'_extend? at hl
  match l with
  | ⟨[], _⟩ => contradiction
  | ⟨b :: bs, hchain⟩ =>
    simp only [Option.dite_none_right_eq_some, Option.some.injEq] at hl
    obtain ⟨hr, rfl⟩ := hl
    simp only [length_cons]

lemma List.suffix_of_Chain'_extend?_eq_some {a : α} {l l' : {l : List α // l.Chain' r}}
    (hl : List.Chain'_extend? r a l = some l') : l.val.IsSuffix l'.val := by
  unfold List.Chain'_extend? at hl
  match l with
  | ⟨[], _⟩ => contradiction
  | ⟨b :: bs, hchain⟩ =>
    simp only [Option.dite_none_right_eq_some, Option.some.injEq] at hl
    obtain ⟨hr, rfl⟩ := hl
    simp only [length_cons]
    exact suffix_cons a (b :: bs)

instance DecidableRel_flip : DecidableRel (flip r) :=
  fun a b => decidable_of_iff' (r b a) (by rfl)

namespace Relation
section finsetChainLength
variable [DecidableEq α] [Fintype α]

instance ReflGenDecidable : DecidableRel (ReflGen r) :=
  fun a b => decidable_of_iff' (b = a ∨ r a b) (Relation.reflGen_iff r a b)

def finsetChainLength_rev (r : α → α → Prop) [DecidableRel r] (a : α) :
    (n : ℕ) → Finset {l : List α // l.Chain' (flip r)}
  | 0 => { ⟨[a], by simp⟩ }
  | n + 1 => Finset.univ.biUnion fun (w : α) =>
    (finsetChainLength_rev r a n).filterMap (fun l => List.Chain'_extend? (flip r) w l)
    (by
    rintro ⟨l1, hl1⟩ ⟨l2, hl2⟩ b hl1 hl2
    simp only [List.Chain'_extend?, Option.mem_def] at hl1 hl2
    cases l1 <;> cases l2 <;> simp_all [Option.ite_none_right_eq_some, Option.some.injEq,
      List.cons.injEq]
    obtain ⟨hl1head, hl1tail⟩ := hl1
    obtain ⟨hl2head, hl2tail⟩ := hl2
    subst hl2tail
    simpa using hl1tail)

def finsetChainLength (r : α → α → Prop) [DecidableRel r] (a : α) (n : ℕ) :
    Finset {l : List α // l.Chain' r} :=
  (finsetChainLength_rev r a n).map ⟨by
    rintro ⟨l, hl⟩
    refine ⟨l.reverse, List.chain'_reverse.mpr hl⟩, by
      rintro ⟨l1, hl1⟩ ⟨l2, hl2⟩ h
      simpa only [Subtype.mk.injEq, List.reverse_inj] using h⟩

lemma ne_nil_of_mem_finsetChainLength {a : α} {n : ℕ} {l : {l : List α // l.Chain' r}}
    (hl : l ∈ finsetChainLength r a n) : l.val ≠ [] := by
  induction' n with n ih <;> unfold finsetChainLength finsetChainLength_rev at hl
  · simp only [Finset.map_singleton, Function.Embedding.coeFn_mk, List.reverse_cons,
      List.reverse_nil, List.nil_append, Finset.mem_singleton] at hl
    subst hl
    simp only [ne_eq, List.cons_ne_self, not_false_eq_true]
  · simp only [Finset.mem_map, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filterMap,
    Subtype.exists, true_and, Function.Embedding.coeFn_mk] at hl
    obtain ⟨L, _hL1, ⟨a, Lrev, _hchain, hLrev, hextend⟩, rfl⟩ := hl
    apply List.ne_nil_of_length_pos
    have := List.length_add_one_eq_of_Chain'_extend?_eq_some hextend
    simp only [List.length_reverse, gt_iff_lt] at this ⊢
    omega

lemma coe_finsetChainLength {a : α} {n : ℕ} : (finsetChainLength r a n : Set _) =
    {l : {l : List α // l.Chain' r} | ∃ h : l.val.length = n+1,
      l.val.head (List.ne_nil_of_length_pos (by omega)) = a} := by
  induction' n with n ih
  · unfold finsetChainLength finsetChainLength_rev
    ext L
    simp only [Finset.map_singleton, Function.Embedding.coeFn_mk, List.reverse_cons,
      List.reverse_nil, List.nil_append, Finset.coe_singleton, Set.mem_singleton_iff, zero_add,
      Set.mem_setOf_eq]
    constructor
    · rintro rfl
      simp [List.getLast_singleton, List.length_singleton, exists_const]
    · rintro ⟨h, rfl⟩
      rw [List.length_eq_one_iff] at h
      obtain ⟨a, hL⟩ := h
      rw [← Subtype.coe_inj]
      simp [hL, List.getLast_singleton]
  · unfold finsetChainLength finsetChainLength_rev
    ext L
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_biUnion, Finset.coe_univ,
      Set.mem_univ, Finset.coe_filterMap, Subtype.exists, Set.iUnion_true, Set.mem_image,
      Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨L, _hL1, ⟨b, Lrev, hchain, hLrev, hextend⟩, rfl⟩
      simp [List.getLast_reverse, List.length_reverse]
      have hLlen := List.length_add_one_eq_of_Chain'_extend?_eq_some hextend
      simp at hLlen
      have : ⟨Lrev.reverse, List.chain'_reverse.mpr hchain⟩ ∈ (finsetChainLength r a n).toSet := by
        unfold finsetChainLength
        simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe,
          Subtype.mk.injEq, List.reverse_inj, Subtype.exists, exists_and_right, exists_eq_right]
        use hchain
      rw [ih] at this
      simp [Set.mem_setOf_eq, List.getLast_reverse, List.length_reverse] at this
      obtain ⟨hL', rfl⟩ := this
      use hL' ▸ hLlen.symm
      have := List.suffix_of_Chain'_extend?_eq_some hextend
      simp at this
      apply (this.getLast _).symm
    · simp only [forall_exists_index]
      rintro hLlen hLhead
      use L.val.reverse
      use (by rw [← List.chain'_reverse, List.reverse_reverse]; exact L.prop)
      simp only [List.reverse_reverse, Subtype.coe_eta, and_true]
      use L.val.getLast (List.ne_nil_of_length_pos (by omega)), L.val.reverse.tail
      use (by rw [← List.chain'_reverse, List.tail_reverse, List.reverse_reverse]; exact L.prop.dropLast)
      constructor
      · suffices ⟨L.val.dropLast, L.prop.init⟩ ∈ finsetChainLength r a n by
          unfold finsetChainLength at this
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.mk.injEq, Subtype.exists,
            exists_and_right] at this
          obtain ⟨Lrev, ⟨H1, H2⟩, hLrev⟩ := this
          convert H2
          simp only [List.tail_reverse]
          exact List.reverse_eq_iff.mpr hLrev.symm
        rw [← Finset.mem_coe, ih]
        simp only [Set.mem_setOf_eq, List.length_dropLast, Nat.pred_eq_succ_iff]
        use hLlen
        rwa [List.head_dropLast]
      · unfold List.Chain'_extend?
        split
        · rename_i l p h
          simp only [List.tail_reverse, Subtype.mk.injEq, List.reverse_eq_nil_iff] at h
          apply_fun List.length at h
          simp only [List.length_dropLast, List.length_nil] at h
          omega
        · rename_i l b bs hchain htail
          simp only [Subtype.mk.injEq, List.reverse_eq_cons_iff] at htail
          have hreverse : L.val.reverse = L.val.getLast (List.ne_nil_of_length_pos (by omega)) :: b :: bs := by
            rw [← htail, ← List.head_reverse]
            refine Eq.symm (List.head_cons_tail L.val.reverse (List.ne_nil_of_length_pos (by simp; omega)))
          have := L.prop
          rw [← L.val.reverse_reverse, List.chain'_reverse, hreverse] at this
          simp only [this.rel_head, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq]
          exact hreverse.symm

lemma mem_finsetChainLength_iff {a : α} {n : ℕ} {l : {l : List α // l.Chain' r}} :
    l ∈ finsetChainLength r a n ↔
    ∃ hlen : l.val.length = n + 1, l.val.head (List.ne_nil_of_length_pos (by omega)) = a := by
  rw [← Finset.mem_coe, coe_finsetChainLength, Set.mem_setOf_eq]

lemma ReflTransGen_iff_exists_finsetChainLength {a b : α} : ReflTransGen r a b ↔
    ∃ (n : Fin (Fintype.card α)) (l : {l : List α // l.Chain' r}) (h : l ∈ finsetChainLength r a n),
    l.val.getLast (ne_nil_of_mem_finsetChainLength h) = b := by
  constructor
  · intro h
    obtain ⟨l, hlChain, hlLast, hnodup⟩ := List.exists_nodup_chain_of_relationReflTransGen h
    use ⟨l.length, ?_⟩, ⟨a :: l, hlChain⟩, ?_
    · have := List.Nodup.length_le_card hnodup
      rw [List.length_cons] at this
      omega
    · rw [mem_finsetChainLength_iff]
      simp only [List.head_cons, List.length_cons, exists_const]
  · rintro ⟨n, l, hl, rfl⟩
    rw [mem_finsetChainLength_iff] at hl
    obtain ⟨hlen, rfl⟩ := hl
    apply l.val.tail.relationReflTransGen_of_exists_chain
    · have hlChain := l.prop
      rwa [← l.val.head_cons_tail] at hlChain
    · simp only [List.head_cons_tail]


instance ReflTransGenDeciable : DecidableRel (ReflTransGen r) := fun a b => by
  apply decidable_of_iff' _ (ReflTransGen_iff_exists_finsetChainLength)

end finsetChainLength


omit [DecidableRel r] in
lemma TransGen.symmetric (h : Symmetric r) : Symmetric (TransGen r) := by
  rintro x y hTG
  induction hTG with
  | single hr => exact single (h hr)
  | tail hTG hr ih => exact head (h hr) ih



def ReflClosure : ClosureOperator (α → α → Prop) where
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

def TransClosure : ClosureOperator (α → α → Prop) where
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

def ReflTransClosure : ClosureOperator (α → α → Prop) where
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

def EqvGenClosure : ClosureOperator (α → α → Prop) where
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

lemma closure_eq_closure_of_le_of_le_closure {r s : α} [PartialOrder α]
  {c : ClosureOperator α} (hle : r ≤ s) (hlec : s ≤ c r) : c r = c s := by
  apply le_antisymm
  · exact c.monotone hle
  · exact le_closure_iff.mp hlec

end ClosureOperator
