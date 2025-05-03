import Mathlib.Data.Setoid.Partition
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Set.Finite.Powerset
-- import Matroid.ForMathlib.Lattice

open Set

variable {α : Type*} {s x y z : α}

@[simp]
lemma Set.ext_iff_simp {α : Type*} {P Q : α → Prop} : {x | P x} = {x | Q x} ↔ ∀ x, P x ↔ Q x :=
  Set.ext_iff

structure Partition (α : Type*) [CompleteLattice α] where
  parts : Set α
  indep : sSupIndep parts
  bot_not_mem : ⊥ ∉ parts

namespace Partition

section Basic

variable [CompleteLattice α] {P : Partition α}

def supp (P : Partition α) : α := sSup P.parts

instance {α : Type*} [CompleteLattice α] : SetLike (Partition α) α where
  coe := Partition.parts
  coe_injective' p p' h := by cases p; cases p'; simpa using h

@[simp] lemma mem_parts {x : α} : x ∈ P.parts ↔ x ∈ (P : Set α) := Iff.rfl

@[ext] lemma ext {P Q : Partition α} (hP : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q := by
  cases P
  cases Q
  simp only [mk.injEq]
  ext x
  simpa using hP x

lemma disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y) :
    Disjoint x y :=
  P.indep.pairwiseDisjoint hx hy hxy

lemma pairwiseDisjoint : Set.PairwiseDisjoint (P : Set α) id :=
  fun _ hx _ hy hxy ↦ P.disjoint hx hy hxy

lemma ne_bot_of_mem (hx : x ∈ P) : x ≠ ⊥ :=
  fun h ↦ P.bot_not_mem <| h ▸ hx

lemma bot_lt_of_mem (hx : x ∈ P) : ⊥ < x :=
  bot_lt_iff_ne_bot.2 <| P.ne_bot_of_mem hx

lemma sSup_eq (P : Partition α) : sSup P = P.supp  := rfl

lemma iSup_eq (P : Partition α) : ⨆ x ∈ P, x = P.supp := by
  simp_rw [← P.sSup_eq, sSup_eq_iSup]
  rfl

lemma le_of_mem (P : Partition α) (hx : x ∈ P) : x ≤ P.supp :=
  (le_sSup hx).trans_eq P.sSup_eq

lemma parts_nonempty (P : Partition α) (hs : P.supp ≠ ⊥) : (P : Set α).Nonempty :=
  nonempty_iff_ne_empty.2 fun hP ↦ by simp [← P.sSup_eq, hP, sSup_empty] at hs

-- @[simps] protected def congr {t : α} (P : Partition s) (hst : s = t) : Partition t where
--   parts := P.parts
--   indep := P.indep
--   bot_not_mem := P.bot_not_mem
--   sSup_eq' := hst ▸ P.sSup_eq'

-- @[simp] lemma coe_congr_eq {t : α} {P : Partition s} (hst : s = t) :
--     (P.congr hst : Set α) = P := rfl

-- @[simp] lemma mem_congr_iff {t x : α} {P : Partition s} (hst : s = t) :
--     x ∈ P.congr hst ↔ x ∈ P := Iff.rfl

-- @[simps!] def partsCongrEquiv {t : α} (P : Partition s) (hst : s = t) :
--     (P : Set α) ≃ (P.congr hst : Set α) := Equiv.setCongr rfl

end Basic

section indep

variable [CompleteLattice α]

/-- A `sSupIndep` collection not containing `⊥` gives a partition of its supremum. -/
@[simps] def ofIndependent {u : Set α} (hs : sSupIndep u) (hbot : ⊥ ∉ u) : Partition α where
  parts := u
  indep := hs
  bot_not_mem := hbot

@[simp] lemma mem_ofIndependent_iff {u : Set α} (hu : sSupIndep u)
    (h : ⊥ ∉ u) {a : α} : a ∈ ofIndependent hu h ↔ a ∈ u := Iff.rfl

@[simp] lemma supp_ofIndependent {u : Set α} (hu : sSupIndep u) (hbot : ⊥ ∉ u) :
    (ofIndependent hu hbot).supp = sSup u := rfl

/-- A `sSupIndep` collection gives a partition of its supremum by removing `⊥`. -/
def ofIndependent' {u : Set α} (hs : sSupIndep u) : Partition α :=
  (ofIndependent (hs.mono (diff_subset (t := {⊥}))) (fun h ↦ h.2 rfl))

@[simp] lemma mem_ofIndependent'_iff {u : Set α} (hu : sSupIndep u) {a : α} :
  a ∈ ofIndependent' hu ↔ a ∈ u ∧ a ≠ ⊥ := Iff.rfl

@[simp] lemma supp_ofIndependent' {u : Set α} (hu : sSupIndep u) :
    (ofIndependent' hu).supp = sSup u := by
  show sSup (u \ {⊥}) = sSup u
  simp

/-- The subpartition with over a subset of the parts. -/
def subpartition (P : Partition α) {s : Set α} (hs : s ⊆ P.parts) : Partition α where
  parts := s
  indep := P.indep.mono hs
  bot_not_mem h := P.bot_not_mem (hs h)

@[simp] lemma subpartition_parts {P : Partition α} {s : Set α} (hs : s ⊆ P.parts) :
    (P.subpartition hs).parts = s := rfl

@[simp] lemma mem_subpartition_iff {P : Partition α} {s : Set α} (hs : s ⊆ P.parts) {a : α} :
    a ∈ P.subpartition hs ↔ a ∈ s := Iff.rfl

/-- The partition with no parts. -/
@[simps] protected def empty (α : Type*) [CompleteLattice α] : Partition α where
  parts := ∅
  indep := by simp
  bot_not_mem := by simp

@[simp] lemma empty_coe_eq (α : Type*) [CompleteLattice α] :
    (Partition.empty α : Set α) = ∅ := rfl

@[simp] lemma not_mem_empty (α : Type*) [CompleteLattice α] {a : α} :
    a ∉ Partition.empty α := by
  rw [← SetLike.mem_coe, empty_coe_eq]
  simp

@[simp] lemma supp_empty (α : Type*) [CompleteLattice α] : (Partition.empty α).supp = ⊥ := by
  simp [Partition.empty, supp]

lemma eq_empty {P : Partition α} (hP : P.supp = ⊥) : P = Partition.empty α := by
  ext x
  have hsup := P.sSup_eq
  simp only [sSup_eq_bot, SetLike.mem_coe, hP] at hsup
  simp only [not_mem_empty, iff_false]
  exact fun hx ↦ P.ne_bot_of_mem hx <| hsup x hx

instance {α : Type*} [CompleteLattice α] [Subsingleton α] : Unique (Partition α) where
  default := Partition.empty α
  uniq P := eq_empty (by
    simp only [← P.sSup_eq, sSup_eq_bot, SetLike.mem_coe]
    exact fun a b ↦ Subsingleton.elim _ _)

/-- The one-part partition. -/
@[simps] def indiscrete (s : α) (hs : s ≠ ⊥) : Partition α where
  parts := {s}
  indep := by simp [sSupIndep]
  bot_not_mem := by simpa using hs.symm

@[simp] lemma mem_indiscrete_iff (s : α) (hs : s ≠ ⊥) {a : α} :
    a ∈ Partition.indiscrete s hs ↔ a = s := Iff.rfl

lemma supp_indiscrete (s : α) (hs : s ≠ ⊥) : (Partition.indiscrete s hs).supp = s := by
  simp [Partition.indiscrete, supp]

end indep

section Order

variable {α : Type*} [CompleteLattice α] {s : α}

instance : PartialOrder (Partition α) where
  le P Q := ∀ x ∈ P, ∃ y ∈ Q, x ≤ y
  lt := _
  le_refl P x hx := by
    refine ⟨x,hx,rfl.le⟩
  le_trans P Q R hPQ hQR x hxP := by
    obtain ⟨y, hy, hxy⟩ := hPQ x hxP
    obtain ⟨z, hz, hyz⟩ := hQR y hy
    exact ⟨z, hz, hxy.trans hyz⟩
  le_antisymm P Q hp hq := by
    refine Partition.ext fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hp x h
      obtain ⟨x', hx', hyx'⟩ := hq y hy
      obtain rfl := PairwiseDisjoint.eq_of_le P.pairwiseDisjoint h hx' (P.ne_bot_of_mem h)
        (hxy.trans hyx')
      rwa [hxy.antisymm hyx']
    obtain ⟨y, hy, hxy⟩ := hq x h
    obtain ⟨x', hx', hyx'⟩ := hp y hy
    obtain rfl := PairwiseDisjoint.eq_of_le Q.pairwiseDisjoint h hx' (Q.ne_bot_of_mem h)
      (hxy.trans hyx')
    rwa [hxy.antisymm hyx']

instance : OrderTop (Partition α) where
  top := ofIndependent' (sSupIndep_singleton ⊤)
  le_top := by
    obtain (hs | hs) := eq_or_ne ⊤ (⊥ : α)
    · have : Subsingleton α := subsingleton_of_bot_eq_top hs.symm
      simp [hs]
    exact fun P x hx ↦ ⟨⊤, by simp [hs], by simp⟩

@[simp] lemma mem_top_iff {a : α} : a ∈ (⊤ : Partition α) ↔ a = ⊤ ∧ a ≠ ⊥ := by
  change a ∈ ofIndependent' (sSupIndep_singleton ⊤) ↔ _
  rw [mem_ofIndependent'_iff, mem_singleton_iff]

lemma top_eq_indiscrete (hs : ⊤ ≠ ⊥) : (⊤ : Partition α) = indiscrete ⊤ hs := by
  ext a
  rw [mem_top_iff, mem_indiscrete_iff, and_iff_left_iff_imp]
  rintro rfl; assumption

lemma parts_top_subset : ((⊤ : Partition α) : Set α) ⊆ {⊤} := by
  simp


end Order
section Bind

variable {α : Type*} [CompleteDistribLattice α]

-- @[simps] protected def bind (P : Partition α) (Qs : ∀ a ∈ P, Partition α)
--     (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp = a) : Partition α where
--   parts := ⋃ a : P, (Qs a a.prop)
--   indep b hb := by
--     simp only [mem_iUnion, SetLike.mem_coe, Subtype.exists] at hb
--     obtain ⟨a, haP, hba : b ∈ Qs a haP⟩ := hb
--     have hdj1 := (Qs a haP).indep hba
--     have hdj2 := (P.indep haP).mono_left <| (Qs a haP).le_of_mem hba
--     refine (hdj1.sup_right hdj2).mono_right ?_
--     simp only [mem_iUnion, SetLike.mem_coe, Subtype.exists, not_exists, mem_parts, ge_iff_le,
--       sSup_le_iff, mem_diff, mem_singleton_iff, and_imp, forall_exists_index]

--     rintro t' x hx (ht' : t' ∈ Qs x hx) hne
--     obtain (rfl | hne) := eq_or_ne x a
--     · exact (le_sSup_of_le (show t' ∈ _ \ {b} from ⟨ht', hne⟩) rfl.le).trans le_sup_left
--     exact (le_sSup_of_le (show x ∈ P.parts \ ({a} : Set α) from ⟨hx, hne⟩)
--       ((Qs x hx).le_of_mem ht')).trans le_sup_right
--   bot_not_mem := by
--     simp only [mem_iUnion, SetLike.mem_coe, Subtype.exists, not_exists]
--     exact fun x hx ↦ (Qs x hx).bot_not_mem
  -- sSup_eq' := by
  --   simp_rw [sSup_iUnion, Partition.sSup_eq, ← P.sSup_eq, sSup_eq_iSup, iSup_subtype]; rfl

-- @[simp] lemma mem_bind_iff {P : Partition s} {Qs : ∀ a ∈ P, Partition a} {a : α} :
--     a ∈ P.bind Qs ↔ ∃ (b : α) (hb : b ∈ P), a ∈ Qs b hb := by
--   change _ ∈ ⋃ _, _ ↔ _; simp

-- @[simp] lemma bind_le {α : Type*} [CompleteDistribLattice α] {s : α} (P : Partition s)
--     (Qs : ∀ a ∈ P, Partition a) : P.bind Qs ≤ P := by
--   intro t ht
--   obtain ⟨b, hbp, h⟩ := mem_bind_iff.1 ht
--   exact ⟨b, hbp, Partition.le_of_mem _ h⟩

end Bind

section Set

variable {s t u : Set α} {P : Partition (Set α)} {x : α}

@[simp] protected lemma sUnion_eq (P : Partition (Set α)) : ⋃₀ P = P.supp :=
  P.sSup_eq

lemma nonempty_of_mem (ht : t ∈ P) : t.Nonempty :=
  nmem_singleton_empty.1 <| P.ne_bot_of_mem ht

lemma subset_of_mem (ht : t ∈ P) : t ⊆ P.supp :=
  P.le_of_mem ht

lemma eq_of_mem_inter (ht : t ∈ P) (hu : u ∈ P) (hx : x ∈ t ∩ u) : t = u :=
  PairwiseDisjoint.elim P.pairwiseDisjoint ht hu fun
    (hdj : Disjoint t u) ↦ by simp [hdj.inter_eq] at hx

lemma eq_of_mem_of_mem (ht : t ∈ P) (hu : u ∈ P) (hxt : x ∈ t) (hxu : x ∈ u) : t = u :=
  eq_of_mem_inter ht hu ⟨hxt, hxu⟩

lemma exists_unique_of_mem_set (P : Partition (Set α)) (hx : x ∈ P.supp) : ∃! t, t ∈ P ∧ x ∈ t := by
  rw [← P.sUnion_eq, mem_sUnion] at hx
  obtain ⟨t, hxt⟩ := hx
  exact ⟨t, hxt, fun u ⟨huP, hxu⟩ ↦ eq_of_mem_inter huP hxt.1 ⟨hxu, hxt.2⟩⟩

lemma subset_sUnion_and_mem_iff_mem {S : Set (Set α)} (hSP : S ⊆ P.parts) :
    t ⊆ ⋃₀ S ∧ t ∈ P ↔ t ∈ S := by
  refine ⟨fun ⟨htsu, htP⟩ ↦ ?_, fun htS ↦ ⟨subset_sUnion_of_mem htS, hSP htS⟩⟩
  obtain ⟨x, hxt⟩ := nonempty_of_mem htP
  obtain ⟨s, hsS, hxs⟩ := htsu hxt
  obtain rfl := eq_of_mem_of_mem htP (hSP hsS) hxt hxs
  exact hsS

@[simp]
lemma subset_sUnion_iff_mem {S : Set (Set α)} (ht : t ∈ P) (hSP : S ⊆ P.parts) :
    t ⊆ ⋃₀ S ↔ t ∈ S := by
  rw [← subset_sUnion_and_mem_iff_mem hSP]
  simp [ht]

/-- The part containing a given element of the set being partitioned. If `x ∉ s`, then `∅`.  -/
def partOf (P : Partition (Set α)) (x : α) : Set α :=
  ⋃₀ {t ∈ P | x ∈ t}

lemma partOf_mem (P : Partition (Set α)) (hx : x ∈ P.supp) : P.partOf x ∈ P := by
  obtain ⟨t, ⟨h', h⟩⟩ := P.exists_unique_of_mem_set hx
  have hrw : {t | t ∈ P ∧ x ∈ t} = {t} := by
    ext t'
    simp only [mem_setOf_eq, mem_singleton_iff]
    exact ⟨h t', by rintro rfl; exact h'⟩
  rw [partOf, hrw, sUnion_singleton]
  exact h'.1

lemma partOf_eq_empty (P : Partition (Set α)) (hx : x ∉ P.supp) : P.partOf x = ∅ := by
  rw [← P.sUnion_eq] at hx
  simp only [partOf, eq_empty_iff_forall_not_mem, mem_sUnion, mem_setOf, not_exists, not_and,
    and_imp]
  exact fun y t ht hxt _ ↦ hx <| mem_sUnion_of_mem hxt ht

lemma mem_partOf (P : Partition (Set α)) (hx : x ∈ P.supp) : x ∈ P.partOf x := by
  obtain ⟨_, ⟨h, -⟩⟩ := P.exists_unique_of_mem_set hx
  exact mem_sUnion_of_mem h.2 h

lemma eq_partOf_of_mem {P : Partition (Set α)} (ht : t ∈ P) (hxt : x ∈ t) :
    t = P.partOf x := by
  have hx : x ∈ P.supp := by
    rw [← P.sUnion_eq]
    exact mem_sUnion_of_mem hxt ht
  obtain ⟨t', ⟨-, h⟩⟩ := P.exists_unique_of_mem_set hx
  rw [h t ⟨ht, hxt⟩, h (P.partOf x) ⟨P.partOf_mem hx, P.mem_partOf hx⟩]

/-- Noncomputably choose a representative from an equivalence class-/
noncomputable def rep (P : Partition (Set α)) (ht : t ∈ P) : α := (P.nonempty_of_mem ht).some

@[simp] lemma rep_mem (ht : t ∈ P) : P.rep ht ∈ t :=
  (P.nonempty_of_mem ht).some_mem

@[simp] lemma rep_mem' (ht : t ∈ P) : P.rep ht ∈ P.supp :=
  P.subset_of_mem ht <| rep_mem ht

@[simp] lemma partOf_rep (ht : t ∈ P) : P.partOf (P.rep ht) = t :=
  (eq_partOf_of_mem ht (P.rep_mem ht)).symm

lemma finite_of_finite (P : Partition (Set α)) (hs : P.supp.Finite) : (P : Set (Set α)).Finite :=
  hs.finite_subsets.subset fun _ ↦ subset_of_mem

@[simps] def ofPairwiseDisjoint {p : Set (Set α)} (h : p.PairwiseDisjoint id) (h_empty : ∅ ∉ p):
    Partition (Set α) where
  parts := p
  indep := PairwiseDisjoint.sSupIndep h
  bot_not_mem := h_empty

lemma ofPairwiseDisjoint_supp {p : Set (Set α)} (h : p.PairwiseDisjoint id) (h_empty : ∅ ∉ p) :
    (ofPairwiseDisjoint h h_empty).supp = ⋃₀ p := rfl

end Set

section Rel

variable {s t : Set α} {a b : α} {P : Partition (Set α)}

lemma symm_iff_of {α : Type*} (r : α → α → Prop) [IsSymm α r] {x y : α} : r x y ↔ r y x :=
  ⟨fun h ↦ symm_of r h, fun h ↦ symm_of r h⟩

lemma refl_of_rel {α : Type*} (r : α → α → Prop) [IsSymm α r] [IsTrans α r] {x y : α}
    (h : r x y) : r x x :=
  trans_of r h (symm_of r h)

/-- A transitive, symmetric Binary relation `r` induces a partition of the set of elements on
  which it is reflexive. -/
@[simps] def ofRel (r : α → α → Prop) [IsTrans α r] [IsSymm α r] : Partition (Set α) where
  parts := ((fun a ↦ {x | r a x}) '' {x | r x x})
  indep := by
    apply PairwiseDisjoint.sSupIndep
    rintro _ ⟨i, -, rfl⟩ _ ⟨j, -,rfl⟩ hij
    refine disjoint_iff_forall_ne.2 ?_
    rintro a (ha : r _ _) _ (hb : r _ _) rfl
    simp only [ne_eq, Set.ext_iff, mem_setOf_eq, not_forall] at hij
    obtain ⟨y, hy⟩ := hij
    exact hy ⟨fun hiy ↦ trans_of r hb (trans_of r (symm_of r ha) hiy),
      fun hjy ↦ trans_of r ha (trans_of r (symm_of r hb) hjy)⟩
  bot_not_mem := by
    simp only [bot_eq_empty, mem_image, mem_setOf_eq, eq_empty_iff_forall_not_mem, not_exists,
      not_and, not_forall, not_not]
    exact fun x hx ↦ ⟨x,hx⟩

variable {r : α → α → Prop} [IsSymm α r] [IsTrans α r] {s : Set α}

@[simp]
lemma ofRel_supp : (ofRel r).supp = {x | r x x} := by
  rw [supp, ofRel, sSup_eq_sUnion, subset_antisymm_iff]
  simp only [sUnion_image, mem_setOf_eq, iUnion_subset_iff, setOf_subset_setOf]
  refine ⟨fun i _ a ha ↦ trans_of r (symm_of r ha) ha, fun i (hi : r i i) ↦ ?_⟩
  simp only [mem_iUnion, mem_setOf_eq, exists_prop]
  exact ⟨i, hi, hi⟩

lemma eqv_class_comm {r : α → α → Prop} [IsSymm α r] (x : α) : {y | r x y} = {y | r y x} := by
  simp_rw [symm_iff_of]

lemma rel_iff_eqv_class_eq_right (hy : r y y) : r x y ↔ {z | r x z} = {z | r y z} := by
  simp_rw [Set.ext_iff, mem_setOf]
  exact ⟨fun hxy z ↦ ⟨fun hxz ↦ trans_of r (symm_of r hxy) hxz,
    fun hyz ↦ trans_of r hxy hyz⟩, fun h ↦ by rwa [h]⟩

lemma rel_iff_eqv_class_eq_left (hx : r x x) : r x y ↔ {z | r x z} = {z | r y z} := by
  rw [symm_iff_of r, rel_iff_eqv_class_eq_right hx, eq_comm]

lemma eqv_class_mem_ofRel (h : r x x) : {y | r x y} ∈ ofRel r :=
  ⟨x, h, rfl⟩

@[simp] lemma mem_ofRel_iff {t : Set α} :
    t ∈ ofRel r ↔ ∃ x, r x x ∧ t = {y | r x y} := by
  simp_rw [eq_comm (a := t)]; rfl

lemma class_nonempty {t : Set α} (ht : t ∈ ofRel r) : t.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := ht; exact ⟨x, hx⟩

@[simp]
lemma ofRel_le_ofRel {r' : α → α → Prop} [IsTrans α r'] [IsSymm α r'] :
    ofRel r ≤ ofRel r' ↔ r ≤ r' := by
  constructor
  · rintro hle a b hrab
    have : r a a := refl_of_rel r hrab
    obtain ⟨S, ⟨z, hz, rfl⟩, hleS⟩ := hle {x | r a x} (mem_ofRel_iff.mpr (by use a, this))
    exact _root_.trans (symm <| hleS this) (hleS hrab)
  · rintro hle S ⟨a, ha, rfl⟩
    use {x | r' a x}, (by rw [mem_ofRel_iff]; use a; simp [hle a a ha]), hle a

/-- Every partition of `s : Set α` induces a transitive, symmetric Binary relation on `α`
  whose equivalence classes are the parts of `P`. The relation is irreflexive outside `s`.  -/
def Rel (P : Partition (Set α)) (a b : α) : Prop :=
  ∃ t ∈ P, a ∈ t ∧ b ∈ t

lemma Rel.exists (h : P.Rel x y) : ∃ t ∈ P, x ∈ t ∧ y ∈ t :=
  h

lemma Rel.forall (h : P.Rel x y) (ht : t ∈ P) : x ∈ t ↔ y ∈ t := by
  obtain ⟨t', ht', hx, hy⟩ := h
  exact ⟨fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hx],
    fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hy]⟩

lemma rel_of_mem_of_mem (ht : t ∈ P) (ha : a ∈ t) (hb : b ∈ t) : P.Rel a b :=
  ⟨t, ht, ha, hb⟩

lemma rel_self_of_mem (ht : t ∈ P) (hx : x ∈ t) : P.Rel x x :=
  rel_of_mem_of_mem ht hx hx

instance (P : Partition (Set α)) : IsSymm α P.Rel where
  symm _ _ := fun ⟨t, ht, ha, hb⟩ ↦ ⟨t, ht, hb, ha⟩

instance (P : Partition (Set α)) : IsTrans α P.Rel where
  trans a b c := fun ⟨t, htP, ha, hb⟩ ⟨t', ht'P, hb', hc'⟩ ↦
    ⟨t, htP, ha, by rwa [eq_of_mem_of_mem htP ht'P hb hb']⟩

lemma Rel.symm {P : Partition (Set α)} (h : P.Rel x y) : P.Rel y x :=
  symm_of P.Rel h

lemma rel_comm {P : Partition (Set α)} : P.Rel x y ↔ P.Rel y x :=
  ⟨Rel.symm, Rel.symm⟩

lemma Rel.trans {P : Partition (Set α)} (hxy : P.Rel x y) (hyz : P.Rel y z) : P.Rel x z :=
  trans_of P.Rel hxy hyz

lemma Rel.mem_left {P : Partition (Set α)} (h : P.Rel x y) : x ∈ P.supp := by
  obtain ⟨t, htP, hxt, -⟩ := h
  exact subset_of_mem htP hxt

lemma Rel.mem_right {P : Partition (Set α)} (h : P.Rel x y) : y ∈ P.supp :=
  h.symm.mem_left

lemma rel_iff_exists : P.Rel x y ↔ ∃ t ∈ P, x ∈ t ∧ y ∈ t := Iff.rfl

lemma rel_iff_partOf_eq_partOf (P : Partition (Set α)) (hx : x ∈ P.supp) (hy : y ∈ P.supp) :
    P.Rel x y ↔ P.partOf x = P.partOf y := by
  refine ⟨fun ⟨t, htP, hxt, hyt⟩ ↦ ?_, fun h ↦ ⟨P.partOf x, P.partOf_mem hx, P.mem_partOf hx, ?_⟩⟩
  · rw [eq_partOf_of_mem (P.partOf_mem hx)]
    rwa [← eq_partOf_of_mem htP hxt]
  rw [h]
  exact mem_partOf P hy

lemma rel_iff_partOf_eq_partOf' (P : Partition (Set α)) :
    P.Rel x y ↔ ∃ (_ : x ∈ P.supp) (_ : y ∈ P.supp), P.partOf x = P.partOf y :=
  ⟨fun h ↦ ⟨h.mem_left, h.mem_right, (P.rel_iff_partOf_eq_partOf h.mem_left h.mem_right).1 h⟩,
    fun ⟨hx,hy,h⟩ ↦ (P.rel_iff_partOf_eq_partOf hx hy).2 h⟩

lemma rel_iff_forall {P : Partition (Set α)} : P.Rel x y ↔ x ∈ P.supp ∧ ∀ t ∈ P, x ∈ t ↔ y ∈ t := by
  refine ⟨fun h ↦ ⟨h.mem_left, fun _ ↦ h.forall⟩,
    fun ⟨hxs, h⟩ ↦ ⟨P.partOf x, P.partOf_mem hxs, P.mem_partOf hxs, ?_⟩⟩
  rw [← h _ (P.partOf_mem hxs)]
  exact P.mem_partOf hxs

lemma setOf_rel_self_eq (P : Partition (Set α)) : {x | P.Rel x x} = P.supp := by
  refine subset_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨t, ht, hxP, -⟩ := hx
    exact subset_of_mem ht hxP
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.exists_unique_of_mem_set hx
  exact ⟨t, ht, hxt, hxt⟩

lemma rel_self_iff_mem {P : Partition (Set α)} : P.Rel x x ↔ x ∈ P.supp := by
  simp [← P.setOf_rel_self_eq]

lemma setOf_rel_eq (ht : t ∈ P) (hx : x ∈ t) : {y | P.Rel x y} = t :=
  Set.ext fun y ↦ ⟨fun ⟨t', ht', hx', hy'⟩ ↦ by rwa [P.eq_of_mem_of_mem ht ht' hx hx'],
    fun h ↦ ⟨t, ht, hx, h⟩⟩

lemma rep_rel (ht : t ∈ P) (hx : x ∈ t) : P.Rel x (P.rep ht) :=
  ⟨t, ht, hx, P.rep_mem ht⟩

@[simp] lemma rep_rel_self {P : Partition (Set α)} (ht : t ∈ P) : P.Rel (P.rep ht) (P.rep ht) :=
  rep_rel _ (P.rep_mem ht)

lemma setOf_rel_rep_eq (ht : t ∈ P) : {x | P.Rel (P.rep ht) x} = t :=
  setOf_rel_eq ht (P.rep_mem ht)

/-- The `partOf x` is the set of `y` related to `x`. True even if `x ∉ s`, since both are `∅`.-/
lemma setOf_rel_eq_partOf (P : Partition (Set α)) (x : α) : {y | P.Rel x y} = P.partOf x := by
  by_cases hx : x ∈ P.supp
  · rw [setOf_rel_eq (P.partOf_mem hx) (P.mem_partOf hx)]
  rw [partOf_eq_empty _ hx, eq_empty_iff_forall_not_mem]
  exact fun y hxy ↦ hx <| Rel.mem_left hxy

lemma setOf_rel_mem (P : Partition (Set α)) (hx : x ∈ P.supp) : {y | P.Rel x y} ∈ P := by
  obtain ⟨t, ⟨ht,hp⟩, -⟩ := P.exists_unique_of_mem_set hx
  rwa [setOf_rel_eq ht hp]

lemma ofRel_rel_eq (P : Partition (Set α)) : ofRel P.Rel = P := by
  ext a
  simp only [mem_ofRel_iff]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact setOf_rel_mem _ hx.mem_right
  obtain ⟨x, hx⟩ := P.nonempty_of_mem h
  exact ⟨x, rel_of_mem_of_mem h hx hx, by rwa [setOf_rel_eq _ hx]⟩

@[simp] lemma rel_ofRel_eq (r : α → α → Prop) [IsTrans α r] [IsSymm α r] : (ofRel r).Rel = r := by
  ext a b
  simp only [Rel, mem_ofRel_iff]
  refine ⟨?_, fun h ↦ ⟨_, ⟨a, refl_of_rel r h, rfl⟩, refl_of_rel r h, h⟩⟩
  rintro ⟨_, ⟨x, -, rfl⟩, ha, hb⟩
  exact trans_of r (symm_of r ha) hb

@[ext] theorem eq_of_rel_iff_rel {P P' : Partition (Set α)} (h : ∀ x y, P.Rel x y ↔ P'.Rel x y) :
    P = P' := by
  rw [← ofRel_rel_eq P, ← ofRel_rel_eq P']; congr; ext; exact h _ _

end Rel

section Discrete

variable {s : Set α} {a b : α}

/-- The discrete partition -/
protected def discrete (s : Set α) : Partition (Set α) :=
  let r : α → α → Prop := fun x y ↦ x = y ∧ x ∈ s
  have : IsTrans α r := ⟨by rintro _ _ _ ⟨rfl, h⟩ ⟨rfl,-⟩; exact ⟨rfl, h⟩⟩
  have : IsSymm α r := ⟨by rintro _ _ ⟨rfl, h⟩; exact ⟨rfl,h⟩⟩
  ofRel r

@[simp] lemma discrete.supp : (Partition.discrete s).supp = s := by
  simp [Partition.discrete]

@[simp] lemma discrete.rel_iff_eq : (Partition.discrete s).Rel a b ↔ a = b ∧ a ∈ s := by
  simp only [Partition.discrete, rel_ofRel_eq]

lemma discrete.rel_iff_eq_of_mem (ha : a ∈ s) : (Partition.discrete s).Rel a b ↔ a = b := by
  rw [discrete.rel_iff_eq, and_iff_left ha]

@[simp] lemma discrete.parts : (Partition.discrete s).parts = ({·}) '' s := by
  ext x
  unfold Partition.discrete
  aesop

end Discrete

section RepFun

variable {a b : α} {P : Partition (Set α)}

structure RepFun (P : Partition (Set α)) where
  (toFun : α → α)
  (apply_eq_self_of_not_mem : ∀ a ∉ P.supp, toFun a = a)
  (rel_apply_of_mem : ∀ a ∈ P.supp, P.Rel a (toFun a))
  (apply_eq_of_rel : ∀ a b, P.Rel a b → toFun a = toFun b)

instance : FunLike (RepFun P) α α where
  coe := RepFun.toFun
  coe_injective' f f' := by cases f; cases f'; simp

@[simp] lemma RepFun.mk_apply (P : Partition (Set α)) (f) (h₁ : ∀ a ∉ P.supp, f a = a)
  (h₂ : ∀ a ∈ P.supp, P.Rel a (f a)) (h₃) (x : α) : (RepFun.mk f h₁ h₂ h₃) x = f x := rfl

lemma RepFun.apply_of_not_mem (f : P.RepFun) (ha : a ∉ P.supp) : f a = a :=
  f.apply_eq_self_of_not_mem a ha

lemma RepFun.rel_apply (f : P.RepFun) (ha : a ∈ P.supp) : P.Rel a (f a) :=
  f.rel_apply_of_mem a ha

lemma RepFun.apply_mem (f : P.RepFun) (ha : a ∈ P.supp) : f a ∈ P.supp :=
  (f.rel_apply ha).mem_right

lemma RepFun.apply_eq_apply (f : P.RepFun) (hab : P.Rel a b) : f a = f b :=
  f.apply_eq_of_rel a b hab

lemma RepFun.rel_of_apply_eq_apply (f : P.RepFun) (ha : a ∈ P.supp) (hab : f a = f b) : P.Rel a b := by
  refine (f.rel_apply ha).trans ?_
  rw [hab, P.rel_comm]
  refine f.rel_apply <| by_contra fun hb ↦ ?_
  rw [f.apply_of_not_mem hb] at hab; rw [← hab] at hb
  exact hb <| f.apply_mem ha

lemma RepFun.rel_of_ne_of_apply_eq_apply (f : P.RepFun) (hne : a ≠ b) (hab : f a = f b) :
    P.Rel a b := by
  obtain (ha | ha) := em (a ∈ P.supp); exact f.rel_of_apply_eq_apply ha hab
  obtain (hb | hb) := em (b ∈ P.supp); exact (f.rel_of_apply_eq_apply hb hab.symm).symm
  rw [f.apply_of_not_mem ha, f.apply_of_not_mem hb] at hab; contradiction

lemma RepFun.apply_eq_apply_iff_rel (f : P.RepFun) (ha : a ∈ P.supp) : f a = f b ↔ P.Rel a b :=
  ⟨f.rel_of_apply_eq_apply ha, f.apply_eq_apply⟩

lemma RepFun.apply_eq_apply_iff_rel_of_ne (f : P.RepFun) (hne : a ≠ b) : f a = f b ↔ P.Rel a b :=
  ⟨f.rel_of_ne_of_apply_eq_apply hne, f.apply_eq_apply⟩

@[simp] lemma RepFun.idem (f : P.RepFun) (a : α) : f (f a) = f a := by
  obtain (ha | ha) := em (a ∈ P.supp)
  · rw [eq_comm, f.apply_eq_apply_iff_rel ha]
    exact f.rel_apply ha
  simp_rw [f.apply_of_not_mem ha]

lemma RepFun.image_subset_self (f : P.RepFun) : f '' P.supp ⊆ P.supp := by
  rintro _ ⟨a,ha,rfl⟩; exact f.apply_mem ha

/-- Any partially defined `RepFun` extends to a complete one. -/
lemma exists_extend_partial_repFun (P : Partition (Set α)) {t : Set α} (f₀ : t → α)
    (h_not_mem : ∀ x : t, x.1 ∉ P.supp → f₀ x = x) (h_mem : ∀ x : t, x.1 ∈ P.supp → P.Rel x (f₀ x))
    (h_eq : ∀ x y : t, P.Rel x y → f₀ x = f₀ y) : ∃ (f : P.RepFun), ∀ x : t, f x = f₀ x := by
  classical
  set f : α → α := fun a ↦ if ha : a ∈ P.supp then
    (if hb : ∃ b : t, P.Rel a b then f₀ hb.choose else P.rep (P.partOf_mem ha)) else a with hf
  refine ⟨RepFun.mk f (fun a ha ↦ by simp [hf, ha]) (fun a ha ↦ ?_) (fun a b hab ↦ ?_), fun a ↦ ?_⟩
  · simp only [hf, exists_prop, ha, ↓reduceDIte]
    split_ifs with h
    · exact h.choose_spec.trans <| h_mem h.choose h.choose_spec.mem_right
    push_neg at h
    exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)
  · simp_rw [hf, dif_pos hab.mem_left, dif_pos hab.mem_right]
    split_ifs with h₁ h₂ h₂
    · exact h_eq _ _ <| (hab.symm.trans h₁.choose_spec).symm.trans h₂.choose_spec
    · exact False.elim <| h₂ ⟨_, hab.symm.trans h₁.choose_spec⟩
    · exact False.elim <| h₁ ⟨_, hab.trans h₂.choose_spec⟩
    congr
    rwa [← rel_iff_partOf_eq_partOf _ hab.mem_left hab.mem_right]
  change f a = f₀ a
  obtain (ha | ha) := em (a.1 ∈ P.supp)
  · simp only [hf, exists_prop, ha, ↓reduceDIte]
    split_ifs with h
    · exact Eq.symm <| h_eq _ _ h.choose_spec
    exact False.elim <| h ⟨a, rel_self_iff_mem.2 ha⟩
  simp [hf, ha, h_not_mem _ ha]

/-- For any set `t` containining no two distinct related elements, there is a `RepFun` equal to
the identity on `t`. -/
lemma exists_extend_partial_repFun' (P : Partition (Set α)) {t : Set α}
    (h : ∀ ⦃x y⦄, x ∈ t → y ∈ t → P.Rel x y → x = y) : ∃ (f : P.RepFun), EqOn f id t := by
  simpa using P.exists_extend_partial_repFun (fun x : t ↦ x) (by simp)
    (by simp [P.rel_self_iff_mem]) (fun x y ↦ h x.2 y.2)

lemma nonempty_repFun (P : Partition (Set α)) : Nonempty P.RepFun := by
  obtain ⟨f, -⟩ := P.exists_extend_partial_repFun' (t := ∅) (by simp)
  exact ⟨f⟩

@[simp] theorem repFun_repFun (f f' : P.RepFun) (x : α) : f (f' x) = f x := by
  obtain (hx | hx) := em (x ∈ P.supp)
  · exact f.apply_eq_apply (f'.rel_apply hx).symm
  rw [f'.apply_of_not_mem hx, f.apply_of_not_mem hx]

@[simp] lemma repFun_discrete_coeFun (s : Set α) (f : (Partition.discrete s).RepFun) :
    (f : α → α) = id := by
  ext x
  obtain (hx | hx) := em (x ∈ s)
  · have hx' := f.rel_apply (by simpa)
    simp only [discrete.rel_iff_eq] at hx'
    exact hx'.1.symm
  rw [f.apply_of_not_mem (by simpa), id]

lemma RepFun.coeFun_eq_id_of_eq_discrete {s : Set α} (f : P.RepFun) (hP : P = Partition.discrete s) :
    (f : α → α) = id := by
  subst hP; exact repFun_discrete_coeFun s f

end RepFun

section Flatten

def flatten (P : Partition (Set (Set α))) (hP : ∃ p : Partition (Set α), p.parts = sSup P.parts) :
    Partition (Set α) where
  parts := sSup '' P.parts
  indep x hx := by
    obtain ⟨p, hp⟩ := hP
    obtain ⟨S, hSP, rfl⟩ := hx
    simp
    rintro T hTP hnex s hsS t hT
    have hSneT : S ≠ T := fun h ↦ by simp [h] at hnex
    have hst : s ≠ t := by
      rintro rfl
      have := P.indep hSP |>.mono_right (by
        simp
        refine subset_sUnion_of_mem (by simpa [hSneT.symm]) : T ≤ _)
      rw [Set.disjoint_left] at this
      exact this hsS hT
    refine (hp ▸ p.indep) (by use S : s ∈ sSup P.parts) |>.mono_right ?_
    simp
    refine subset_sUnion_of_mem ?_
    simp [hst.symm]
    use T
  bot_not_mem := by
    simp
    rintro S hS
    have hSne : S.Nonempty := by
      have := P.bot_not_mem
      simp only [bot_eq_empty, mem_parts, SetLike.mem_coe] at this
      exact nonempty_of_mem hS
    obtain ⟨x, hx⟩ := hSne
    use x, hx
    rintro rfl
    obtain ⟨p, hp⟩ := hP
    have := p.bot_not_mem
    simp only [bot_eq_empty, mem_parts, SetLike.mem_coe] at this
    refine this (?_ : ∅ ∈ p.parts)
    rw [hp]
    use S, hS

@[simp]
lemma flatten_parts {P : Partition (Set (Set α))}
    {hP : ∃ p : Partition (Set α), p.parts = sSup P.parts} :
    (flatten P hP).parts = sSup '' P.parts := rfl

-- def Flatten' (P : Partition (Set α)) (hP : ∃ p : Partition α, p.parts = sSup P.parts) :
--     Partition α where
--   parts := sSup '' P.parts
--   indep x hx := by
--     obtain ⟨p, hp⟩ := hP
--     obtain ⟨S, hSP, rfl⟩ := hx
--     rintro a haS ha
--     have := P.indep hSP
--     have hSneT : S ≠ T := fun h ↦ by simp [h] at hnex
--     have hst : s ≠ t := by
--       rintro rfl
--       have := P.indep hSP |>.mono_right (by
--         simp
--         refine subset_sUnion_of_mem (by simpa [hSneT.symm]) : T ≤ _)
--       rw [Set.disjoint_left] at this
--       exact this hsS hT
--     refine (hp ▸ p.indep) (by use S : s ∈ sSup P.parts) |>.mono_right ?_
--     simp
--     refine subset_sUnion_of_mem ?_
--     simp [hst.symm]
--     use T
--   bot_not_mem := by
--     simp
--     rintro S hS
--     have hSne : S.Nonempty := by
--       have := P.bot_not_mem
--       simp only [bot_eq_empty, mem_parts, SetLike.mem_coe] at this
--       exact nonempty_of_mem hS
--     obtain ⟨x, hx⟩ := hSne
--     use x, hx
--     rintro rfl
--     obtain ⟨p, hp⟩ := hP
--     have := p.bot_not_mem
--     simp only [bot_eq_empty, mem_parts, SetLike.mem_coe] at this
--     refine this (?_ : ∅ ∈ p.parts)
--     rw [hp]
--     use S, hS

end Flatten


-- def ConnectedPartition (G : Graph α β) : Partition G.V := Partition.ofRel (G.VxConnected)

-- def Component (G : Graph α β) (v : α) := {u | G.VxConnected v u}

-- def ComponentSets (G : Graph α β) (V : Set α) := Component G '' V

-- @[simp]
-- lemma connectedPartition_supp : G.ConnectedPartition.supp = G.V := by
--   simp [ConnectedPartition]

-- @[simp↓] lemma connectedPartition_sSup : sSup G.ConnectedPartition.parts = G.V :=
--   connectedPartition_supp
-- @[simp↓] lemma connectedPartition_sUnion : ⋃₀ G.ConnectedPartition.parts = G.V :=
--   connectedPartition_supp

-- @[simp]
-- lemma connectedPartition_parts : G.ConnectedPartition.parts = G.ComponentSets G.V := by
--   ext S
--   simp only [ConnectedPartition, ofRel_parts, vxConnected_self, setOf_mem_eq, mem_image,
--     ComponentSets, Component, mem_setOf_eq]

-- @[simp]
-- lemma set_spec_connected_comm : {x | G.VxConnected x y} = {x | G.VxConnected y x} := by
--   simp_rw [vxConnected_comm]

-- lemma set_spec_connected_eq_componentSet : {x | G.VxConnected y x} = G.Component y := rfl

-- @[simp]
-- lemma component_eq_empty : G.Component x = ∅ ↔ x ∉ G.V := by
--   constructor
--   · intro h hx
--     rw [← mem_empty_iff_false, ← h]
--     exact VxConnected.refl hx
--   · intro h
--     ext y
--     simp [Component, h]

-- @[simp]
-- lemma component_subset_V : G.Component x ⊆ G.V := fun _y hy ↦ hy.mem_right

-- @[simp]
-- lemma component_eq_component (hx : x ∈ G.V) : G.Component x = G.Component y ↔ G.VxConnected x y :=
--   (rel_iff_eqv_class_eq_left (VxConnected.refl hx)).symm

-- @[simp]
-- lemma component_eq_component' (hy : y ∈ G.V) : G.Component x = G.Component y ↔ G.VxConnected x y := by
--   rw [eq_comm, vxConnected_comm, component_eq_component hy]

-- @[simp]
-- lemma component_mem_partition : G.Component x ∈ G.ConnectedPartition ↔ x ∈ G.V := by
--   refine mem_ofRel_iff.trans ?_
--   simp +contextual only [vxConnected_self, set_spec_connected_eq_componentSet, iff_def,
--     forall_exists_index, and_imp, component_eq_component', component_eq_component]
--   refine ⟨fun y hy hconn ↦ hconn.mem_left, fun h ↦ ?_⟩
--   use x, h, VxConnected.refl h

-- @[simp] lemma mem_component_iff : y ∈ G.Component x ↔ G.VxConnected x y := by rfl

-- lemma mem_component_iff' : y ∈ G.Component x ↔ G.VxConnected y x := by
--   rw [vxConnected_comm, mem_component_iff]

-- -- @[simp] lemma ComponentSet.self_mem : x ∈ G.ComponentSet x ↔ x ∈ G.V := by simp

-- -- @[simp]
-- -- lemma component_mem_componentSets (hx : x ∈ G.V) :
-- --     G.Component x ∈ G.ComponentSets T ↔ ∃ y ∈ T, G.VxConnected x y := by
-- --   simp only [ComponentSets, mem_image, hx, component_eq_component']
-- --   simp_rw [vxConnected_comm]

-- -- lemma componentSets_component (hx : x ∈ G.V) :
-- --     G.ComponentSets (G.Component x) = {G.Component x} := by
-- --   ext S
-- --   simp +contextual only [mem_singleton_iff, iff_def, component_mem_componentSets hx,
-- --     mem_component_iff, and_self]

-- --   rintro ⟨y, hy, rfl⟩
-- --   simpa [hx, vxConnected_comm] using hy

-- -- @[simp]
-- -- lemma ComponentSets.sUnion_V : ⋃₀ G.ComponentSets G.V = G.V := by
-- --   rw [← ConnectedPartition.parts]
-- --   exact ConnectedPartition.supp

-- -- @[simp] lemma ComponentSets.sSup_V : sSup (G.ComponentSets G.V) = G.V := sUnion_V

-- lemma ConnectedPartition.le (hle : G ≤ H) : G.ConnectedPartition ≤ H.ConnectedPartition := by
--   simpa [ConnectedPartition] using fun u v ↦ (VxConnected.of_le · hle)

-- @[simp]
-- lemma ConnectedPartition.Rel : G.ConnectedPartition.Rel = G.VxConnected := by
--   unfold ConnectedPartition
--   rw [rel_ofRel_eq]
