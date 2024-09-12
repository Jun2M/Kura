import Mathlib.Data.Finset.Slice


-- instance Prod.DecidableEq [DecidableEq α] [DecidableEq β] : DecidableEq (α × β) := by infer_instance

def Multiset.attachWith {α : Type*} (s : Multiset α) (P : α → Prop) (H : ∀ (x : α), x ∈ s → P x) :
  Multiset {x // P x} :=
  s.pmap Subtype.mk H

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
