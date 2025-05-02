import Mathlib.Data.Finset.Slice
import Mathlib.Data.Finset.Sort
import Kura.Dep.List
import Mathlib.Data.Set.Card


variable {α β: Type*}

lemma Set.not_injOn_of_card_lt_card {s : Set α} {hs : s.Finite} {f : α → β}
    {hrange : (Set.range f).Finite} (h : hrange.toFinset.card < hs.toFinset.card) :
    ¬ Set.InjOn f s := by
  intro hinj
  have := hinj.encard_image
  rw [Set.Finite.encard_eq_coe_toFinset_card ((finite_image_iff hinj).mpr hs),
    Set.Finite.encard_eq_coe_toFinset_card hs] at this
  simp only [Nat.cast_inj] at this
  rw [← this] at h; clear this
  apply not_le_of_lt h
  apply Finset.card_le_card
  simp only [Finite.subset_toFinset, Finite.coe_toFinset, image_subset_iff, preimage_range,
    subset_univ]

namespace Multiset

def attachWith (s : Multiset α) (P : α → Prop) (H : ∀ (x : α), x ∈ s → P x) :
  Multiset {x // P x} :=
  s.pmap Subtype.mk H

def eraseNone (s : Multiset (Option α)) : Multiset α :=
  (s.filter (Option.isSome ·)).attach |>.map (fun x => Option.get x.1 (by exact (mem_filter.mp x.2).2))

lemma ne_of_card_ne (s t : Multiset α) (h : Multiset.card s ≠ Multiset.card t) : s ≠ t := by
  intro hst
  exact (hst ▸ h) rfl

-- @[simp]
-- lemma zero_ne_singleton (a : α) : (0 : Multiset α) ≠ {a} := (singleton_ne_zero a).symm
-- appearently added to the Mathlib

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

-- lemma attachWith_map_val' [DecidableEq α] {s : Multiset α} {P : α → Prop}
--   (H : ∀ (x : α), x ∈ s → P x) (f : α → β) :
--     (s.attachWith P H).map (f ·.val) = s.map f := by
--   apply Quot.inductionOn
--   rintro l
--   -- have := List.attachWith_map_val
--   sorry

-- @[simp]
-- lemma attachWith_map_val [DecidableEq α] (s : Multiset α) {P : α → Prop}
--   (H : ∀ (x : α), x ∈ s → P x) : (s.attachWith P H).map Subtype.val = s := by
--   -- exact Quot.induction (fun l => (attachWith_map_val' H Subtype.val).symm) s
--   sorry

@[simp]
lemma sizeOf_coe (l : List α) : sizeOf (l : Multiset α) = sizeOf l := rfl

lemma sizeOf_filter_le (s : Multiset α) (p : α → Prop) [DecidablePred p] :
  sizeOf (s.filter p) ≤ sizeOf s := by
  induction' s using Quot.inductionOn with l
  simp only [quot_mk_to_coe'', Multiset.filter_coe p l, sizeOf_coe, List.sizeOf_filter_le]

lemma sizeOf_filter_lt {p : α → Prop} [DecidablePred p] (s : Multiset α) {b : α} (hs : b ∈ s)
  (hp : ¬ p b) : sizeOf (s.filter p) < sizeOf s := by
  induction' s using Quot.inductionOn with l
  simp only [quot_mk_to_coe'', filter_coe, sizeOf_coe, l.sizeOf_filter_lt hs hp]

lemma sizeOf_filter_le_filter {p q : α → Prop} [DecidablePred p] [DecidablePred q]
  (hpq : ∀ a, p a → q a) (s : Multiset α) : sizeOf (s.filter p) ≤ sizeOf (s.filter q) := by
  induction' s using Quot.inductionOn with l
  simp only [quot_mk_to_coe'', filter_coe, sizeOf_coe, List.sizeOf_filter_le_filter hpq]

lemma sizeOf_filter_lt_filter {p q : α → Prop} [DecidablePred p] [DecidablePred q]
  (hpq : ∀ a, p a → q a) (s : Multiset α) {b : α} (hs : b ∈ s) (hp : ¬ p b) (hq : q b) :
  sizeOf (s.filter p) < sizeOf (s.filter q) := by
  induction' s using Quot.inductionOn with l
  simp only [quot_mk_to_coe'', filter_coe, sizeOf_coe, l.sizeOf_filter_lt_filter hpq
    (by simpa using hs) hp hq]


lemma pair_eq_pair_iff {a b c d : α} :
    ({a, b} : Multiset α) = {c, d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  constructor
  · intro h
    have ha : a ∈ ({a, b} : Multiset α) := by simp
    simp only [h, insert_eq_cons, mem_cons, mem_singleton] at ha
    obtain rfl | rfl := ha
    · simp_all only [insert_eq_cons, cons_inj_right, singleton_inj, and_self, true_or]
    · rw [pair_comm] at h
      simp_all only [insert_eq_cons, cons_inj_left, and_self, or_true]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [pair_comm]

@[simp]
lemma map_eq_pair_iff {f : α → β} {s : Multiset α} {c d : β} :
    s.map f = {c, d} ↔ ∃ a b, s = {a, b} ∧ f a = c ∧ f b = d := by
  classical
  simp_rw [insert_eq_cons, ← map_eq_cons, map_eq_singleton]
  constructor
  · rintro ⟨a, ha, rfl, b, hb, rfl⟩
    use a, b, ?_
    rw [← cons_erase ha, hb]
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    use a, (by simp), rfl, b, (by simp)

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

variable {V : Type*}

instance Fintype.subtypeOfFintype [Fintype V] (P : V → Prop) [DecidablePred P] : Fintype {v // P v} where
  elems := Finset.attachWith (Finset.univ.filter P) P (by simp only [Finset.mem_filter,
    Finset.mem_univ, true_and, imp_self, implies_true])
  complete := Fintype.complete

noncomputable instance Fintype.ofFiniteSet {s : Set V} [Finite s] : Fintype s :=
  (@Fintype.ofFinite _ s.toFinite)

lemma ncard_eq_card (s : Set V) [Finite s] : s.ncard = Fintype.card s := by
  have := s.toFinite.card_toFinset
  convert this
  exact s.ncard_eq_toFinset_card s.toFinite
