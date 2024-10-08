import Mathlib.Data.Finset.Slice
import Mathlib.Data.Finset.Sort


namespace Multiset
variable {α : Type*}

def attachWith (s : Multiset α) (P : α → Prop) (H : ∀ (x : α), x ∈ s → P x) :
  Multiset {x // P x} :=
  s.pmap Subtype.mk H

def eraseNone (s : Multiset (Option α)) : Multiset α :=
  (s.filter (Option.isSome ·)).attach |>.map (fun x => Option.get x.1 (by exact (mem_filter.mp x.2).2))

lemma ne_of_card_ne (s t : Multiset α) (h : Multiset.card s ≠ Multiset.card t) : s ≠ t := by
  intro hst
  exact (hst ▸ h) rfl

@[simp]
lemma zero_ne_singleton (a : α) : (0 : Multiset α) ≠ {a} := (singleton_ne_zero a).symm

lemma union_assoc [DecidableEq α] (s t u : Multiset α) : s ∪ t ∪ u = s ∪ (t ∪ u) := by
  ext a
  simp only [count_union]
  exact max_assoc _ _ _

instance instMultisetUnionCommutative [DecidableEq α]: Std.Commutative (fun (s t : Multiset α) => s ∪ t) := ⟨union_comm⟩
instance instMultisetUnionAssociative [DecidableEq α]: Std.Associative (α := Multiset α) (· ∪ ·) := ⟨union_assoc⟩

instance instMultisetAddCommutative [DecidableEq α]: Std.Commutative (fun (s t : Multiset α) => s + t) := ⟨add_comm⟩
instance instMultisetAddAssociative [DecidableEq α]: Std.Associative (α := Multiset α) (· + ·) := ⟨add_assoc⟩

@[simp]
lemma inter_self (s : Multiset α) [DecidableEq α] : s ∩ s = s := by
  ext a
  simp only [count_inter]
  exact min_self _

lemma ne_zero_of_mem {s : Multiset α} {a : α} (h : a ∈ s) : s ≠ 0 := by
  intro h0
  rw [h0] at h
  exact not_mem_zero a h

end Multiset

namespace Finset
variable {α : Type*}

lemma disjUnion_compl_eq_univ {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) :
  s.disjUnion sᶜ disjoint_compl_right = Finset.univ := by simp

def attachWith {α : Type*} (s : Finset α) (P : α → Prop) (H : ∀ (x : α), x ∈ s → P x) :
  Finset {x // P x} where
  val := Multiset.attachWith s.val P H
  nodup := s.nodup.pmap (by simp only [Subtype.mk.injEq, imp_self, implies_true])

end Finset

instance Fintype.subtypeOfFintype [Fintype V] (P : V → Prop) [DecidablePred P] : Fintype {v // P v} where
  elems := Finset.attachWith (Finset.univ.filter P) P (by simp only [Finset.mem_filter,
    Finset.mem_univ, true_and, imp_self, implies_true])
  complete := Fintype.complete
