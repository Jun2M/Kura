import Kura.Dep.Sym2
import Mathlib.Data.Multiset.Sort

open Mathlib

-- class ComparableTotalOrder (α : Type*) extends PartialOrder α, IsTotal α (·≤·) where
--   dec : DecidableRel (·≤·: α → α → Prop)

def SortedLen (α : Type u) (r : α → α → Prop) (n : ℕ) : Type u :=
  { l : List α // l.Sorted r ∧ l.length = n }

class IsSymmetric (r : α → α → Prop) where
  symm : Symmetric r

class IsAntiSymmetric (r : α → α → Prop) where
  antisymm : AntiSymmetric r

class IsReflexive (r : α → α → Prop) where
  refl : Reflexive r

section
variable {α : Type*} {r : α → α → Prop} {n : ℕ} [IsReflexive r] [IsAntiSymmetric r] [DecidableRel r]

---------------------------------------------------

end

def _orderd_Vector (α : Type u) (n : ℕ) [PartialOrder α] : Type u :=
  { l : Vector α n // l.toList.Sorted (·≤·) }

def OrderedLen (α : Type u) [PartialOrder α] (n : ℕ) : Type u :=
  { l : List α // l.Sorted (·≤·) ∧ l.length = n }

def _ordered_len (α : Type u) [PartialOrder α] (n : ℕ) : Type u :=
  let P : Type u := { l : List α // l.Sorted (·≤·) }
  { l : P // l.1.length = n}


namespace OrderedLen

section
variable {α : Type*} [PartialOrder α] [DecidableRel (·≤·: α → α → Prop)]
  [IsTotal α (·≤·)] {n : ℕ}

def toVector (l : OrderedLen α n) : Vector α n := ⟨l.val, l.property.2⟩

instance : Coe (OrderedLen α n) (Vector α n) := ⟨toVector⟩

def toList (l : OrderedLen α n) : List α := l.val

@[ext]
theorem ext {l₁ l₂ : OrderedLen α n} (h : l₁.val = l₂.val) : l₁ = l₂ :=
  Subtype.ext h

@[simp]
theorem ext_iff (l₁ l₂ : OrderedLen α n) : l₁ = l₂ ↔ l₁.val = l₂.val :=
  Iff.intro (congrArg _) Subtype.ext

theorem EquivOrederedLen_ordered_vector : _orderd_Vector α n ≃ OrderedLen α n where
  toFun := λ l => ⟨l.val.toList, l.property, Vector.toList_length l.val⟩
  invFun := λ l => ⟨⟨l.val, l.property.2⟩, l.property.1⟩
  left_inv := λ _ => Subtype.ext rfl
  right_inv := λ _ => Subtype.ext rfl

theorem Equiv_ordered_Vector_ordered_len : _orderd_Vector α n ≃ _ordered_len α n where
  toFun := λ l => ⟨⟨l.val.toList, l.property⟩, Vector.toList_length l.val⟩
  invFun := λ l => ⟨⟨l.val, l.property⟩, l.val.property⟩
  left_inv := λ _ => Subtype.ext rfl
  right_inv := λ _ => Subtype.ext rfl

theorem EquivOrederedLen_ordered_len : OrderedLen α n ≃ _ordered_len α n where
  toFun := λ l => ⟨⟨l.val, l.property.1⟩, l.property.2⟩
  invFun := λ l => ⟨l.val, ⟨l.val.property, l.property⟩⟩
  left_inv := λ _ => Subtype.ext rfl
  right_inv := λ _ => Subtype.ext rfl

theorem EquivOrderedLenSym : OrderedLen α n ≃ Sym α n where
  toFun := λ l => by
    refine ⟨l.val, ?_⟩
    simp [l.property.2]
  invFun := λ l => ⟨l.val.sort (·≤·), ⟨by simp, by simp_all⟩⟩
  left_inv := λ l => by
    obtain ⟨l, h₁, h₂⟩ := l
    simp [List.mergeSort_eq_self _ h₁]
  right_inv := λ l => by
    obtain ⟨l, h⟩ := l
    simp

theorem EquivOrderedLenSym2 : OrderedLen α 2 ≃ Sym2 α :=
  EquivOrderedLenSym.trans (Sym2.equivSym α).symm

end

end OrderedLen

def OrderedLen2 (α : Type u) [LinearOrder α] : Type u :=
  {p : α × α // p.1 ≤ p.2}

namespace OrderedLen2
variable {α : Type*} [LinearOrder α] (o : OrderedLen2 α) (a b : α)

@[simp] def toPair (o : OrderedLen2 α) : α × α := o.val

instance : Coe (OrderedLen2 α) (α × α) := ⟨toPair⟩

@[simp] def fst : α := o.val.1
@[simp] def snd : α := o.val.2
@[simp] def property' : o.fst ≤ o.snd := o.property

theorem coe_eq_fst_snd (o : OrderedLen2 α) : (o.fst, o.snd) = o.toPair := by rfl

@[simp] def mk' : OrderedLen2 α := by
  by_cases h : a ≤ b
  · exact ⟨(a, b), h⟩
  · exact ⟨(b, a), le_of_not_le h⟩

@[simp] def mk (a b : α) (h : a ≤ b) : OrderedLen2 α := ⟨(a, b), h⟩

@[ext] theorem ext (o' : OrderedLen2 α) (h : o.toPair = o'.toPair) : o = o' := by
  cases o; cases o'
  simp_all

@[simp] theorem ext_iff (o' : OrderedLen2 α) : o = o' ↔ o.toPair = o'.toPair := by
  apply Iff.intro
  · intro h; simp [h]
  · intro h; exact ext o o' h

@[simp] theorem mk_toPair (h : a ≤ b) : (mk a b h).toPair = (a, b) := rfl

@[simp] theorem mk'_toPair : (mk' a b).toPair = if a ≤ b then (a, b) else (b, a) := by
  rw []
  by_cases h : a ≤ b <;> simp [h]

@[simp] theorem toPair_mk' : mk' (o.toPair).fst (o.toPair).snd = o  := by
  simp
  intro h
  exfalso
  exact not_lt_of_le o.property h

-- theorem toPair_mk : mk (o.toPair).fst (o.toPair).snd o.property = o := by simp

theorem mk'_swap : mk' a b = mk' b a := by
  obtain h | h | h := lt_trichotomy a b
  · simp [h.le, not_le_of_gt h]
  · simp [h]
  · simp [h.le, not_le_of_gt h]

-- theorem toPair_mk_eq (h : a ≤ b) : o.toPair = (a, b) ↔ o = mk a b h := by simp

theorem mk_eq_mk' (h₁ : a ≤ b) : mk a b h₁ = mk' a b := by simp [h₁]

theorem EquivOrdered2Sym2 : OrderedLen2 α ≃ Sym2 α where
  toFun := λ o => s(o.fst, o.snd)
  invFun := λ s => mk' s.out.1 s.out.2
  left_inv := λ o => by
    simp_all only [mk', Prod.mk.eta, ext_iff, toPair]
    obtain h | h := Sym2.out_mk_eq_or_swap o.fst o.snd
    · simp only [h, o.property', ↓reduceDite]
      rfl
    · rw [h]
      obtain hlt | heq := lt_or_eq_of_le o.property'
      · simp only [not_le_of_lt hlt, ↓reduceDite]
        rfl
      · simp only [heq, le_refl, ↓reduceDite]
        nth_rewrite 1 [← heq]
        rfl
  right_inv := λ s => by
    simp only [mk', Prod.mk.eta]
    by_cases h : s.out.1 ≤ s.out.2
    · simp only [fst, h, ↓reduceDite, snd, Prod.mk.eta, Quot.out_eq]
    · simp only [fst, h, ↓reduceDite, snd, Sym2.eq_swap, Prod.mk.eta, Quot.out_eq]

end OrderedLen2
