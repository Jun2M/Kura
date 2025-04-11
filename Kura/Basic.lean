import Mathlib.Data.Set.Card
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.ENat
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Algebra.BigOperators.Sym
import Kura.Dep.SetPartition
import Kura.Dep.Sym2
import Kura.Dep.Finset

open Finsupp Set Function

/-- This lemma should be in mathlib. -/
@[simp]
lemma finsum_mem_const {α M : Type*} (s : Set α) [AddCommMonoid M] (c : M) :
    ∑ᶠ x ∈ s, c = s.ncard • c := by
  obtain h | h := s.finite_or_infinite
  · rw [finsum_mem_eq_finite_toFinset_sum _ h, Set.ncard_eq_toFinset_card _ h]
    simp only [Finset.sum_const]
  obtain rfl | hne := eq_or_ne c 0
  · simp only [finsum_zero, smul_zero]
  rw [finsum_mem_eq_zero_of_infinite, h.ncard, zero_smul]
  simpa only [Function.support_const hne, Set.inter_univ]

/-- A graph where incidence is described by a map from `β` to `α →₀ ℕ`.
`incFun e` is the column of the incidence matrix at `e`, where loops give value `2`. -/
@[ext] structure Graph (α β : Type*) where
  V : Set α
  E : Set β
  incFun : β → α →₀ ℕ
  sum_eq : ∀ ⦃e⦄, e ∈ E → (incFun e).sum (fun _ x ↦ x) = 2
  vertex_support : ∀ ⦃e v⦄, incFun e v ≠ 0 → v ∈ V
  edge_support : ∀ ⦃e v⦄, incFun e v ≠ 0 → e ∈ E

variable {α α' β β' : Type*} {G : Graph α β} {x y v w : α} {e f : β}

namespace Graph

protected class Finite (G : Graph α β) : Prop where
  vx_fin : G.V.Finite
  edge_fin : G.E.Finite

instance instvxFinite [G.Finite] : G.V.Finite := Finite.vx_fin

instance instedgeFinite [G.Finite] : G.E.Finite := Finite.edge_fin

/-- Incidence -/
def Inc (G : Graph α β) (e : β) (x : α) : Prop := G.incFun e x ≠ 0

def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.incFun e x = 2

def IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop := G.incFun e x = 1

@[simp]
lemma incFun_eq_one : G.incFun e x = 1 ↔ G.IsNonloopAt e x := Iff.rfl

@[simp]
lemma incFun_eq_two : G.incFun e x = 2 ↔ G.IsLoopAt e x := Iff.rfl

lemma Inc.vx_mem (h : G.Inc e x) : x ∈ G.V :=
  G.vertex_support h

@[simp]
lemma not_inc_of_not_vx_mem (h : x ∉ G.V) : ¬ G.Inc e x :=
  by_contra fun h' ↦ h <| (not_not.mp h').vx_mem

lemma Inc.edge_mem (h : G.Inc e x) : e ∈ G.E :=
  G.edge_support h

@[simp]
lemma not_inc_of_not_edge_mem (h : e ∉ G.E) : ¬ G.Inc e x :=
  by_contra fun h' ↦ h <| (not_not.mp h').edge_mem

lemma Inc.iff_mem_support : G.Inc e x ↔ x ∈ (G.incFun e).support := by
  unfold Inc
  rw [Finsupp.mem_support_iff]

@[simp]
lemma incFun_of_not_mem_edgeSet (he : e ∉ G.E) : G.incFun e = 0 := by
  simp_rw [DFunLike.ext_iff]
  exact fun x ↦ by_contra fun h' ↦ he <| G.edge_support h'

lemma incFun_of_not_mem_vertexSet (hv : v ∉ G.V) (e) : G.incFun e v = 0 :=
  by_contra fun h' ↦ hv <| G.vertex_support h'

@[simp]
lemma incFun_eq_zero : G.incFun e x = 0 ↔ ¬ G.Inc e x := by
  rw [iff_not_comm]
  rfl

lemma incFun_ne_zero : G.incFun e x ≠ 0 ↔ G.Inc e x := Iff.rfl

lemma incFun_le_two (G : Graph α β) (e) (v) : G.incFun e v ≤ 2 := by
  refine (em (G.Inc e v)).elim (fun h ↦ ?_) (fun h ↦ by simp only [incFun_eq_zero.2 h, zero_le])
  rw [← G.sum_eq h.edge_mem, Finsupp.sum]
  exact Finset.single_le_sum (by simp) (by simpa)

lemma incFun_eq_zero_or_one_or_two (G : Graph α β) (e) (v) :
    G.incFun e v = 0 ∨ G.incFun e v = 1 ∨ G.incFun e v = 2 := by
  have := G.incFun_le_two e v
  omega

lemma IsLoopAt.inc (h : G.IsLoopAt e v) : G.Inc e v := by
  rw [IsLoopAt] at h
  simp only [← incFun_ne_zero, h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

lemma IsLoopAt.vx_mem (h : G.IsLoopAt e v) : v ∈ G.V := G.vertex_support h.inc

lemma IsLoopAt.edge_mem (h : G.IsLoopAt e v) : e ∈ G.E := G.edge_support h.inc

lemma IsNonloopAt.inc (h : G.IsNonloopAt e v) : G.Inc e v := by
  rw [IsNonloopAt] at h
  simp only [← incFun_ne_zero, h, ne_eq, one_ne_zero, not_false_eq_true]

lemma IsNonloopAt.vx_mem (h : G.IsNonloopAt e v) : v ∈ G.V := G.vertex_support h.inc

lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e v) : e ∈ G.E := G.edge_support h.inc

lemma inc_iff_isLoopAt_or_isNonloopAt :
    G.Inc e v ↔ G.IsLoopAt e v ∨ G.IsNonloopAt e v := by
  rw [← incFun_ne_zero, IsLoopAt, IsNonloopAt]
  have h := G.incFun_le_two e v
  omega

alias ⟨Inc.isLoopAt_or_isNonloopAt, _⟩ := inc_iff_isLoopAt_or_isNonloopAt

lemma isLoopAt_iff : G.IsLoopAt e v ↔ G.Inc e v ∧ ∀ x, G.Inc e x → x = v := by
  classical
  wlog hev : G.Inc e v
  · exact iff_of_false (fun h ↦ hev h.inc) (by simp only [hev, false_and, not_false_eq_true])
  rw [IsLoopAt, ← G.sum_eq hev.edge_mem, Finsupp.sum,
    Finset.sum_eq_sum_diff_singleton_add (i := v) (by simpa only [Finsupp.mem_support_iff, ne_eq,
      incFun_eq_zero, Decidable.not_not])]
  aesop

lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e v) (h_inc : G.Inc e x) : x = v :=
  (isLoopAt_iff.1 h).2 _ h_inc

lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e v) : ¬ G.IsLoopAt e v := by
  rw [IsNonloopAt] at h
  simp only [IsLoopAt, h, OfNat.one_ne_ofNat, not_false_eq_true]

lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e v) : ¬ G.IsNonloopAt e v := by
  rw [IsLoopAt] at h
  simp only [IsNonloopAt, h, OfNat.ofNat_ne_one, not_false_eq_true]

lemma IsNonloopAt.exists_inc_ne (h : G.IsNonloopAt e v) : ∃ w, G.Inc e w ∧ w ≠ v := by
  simpa [ne_eq, isLoopAt_iff, and_iff_right h.inc, not_forall, Classical.not_imp] using
    h.not_isLoopAt

lemma isNonloopAt_iff : G.IsNonloopAt e v ↔ G.Inc e v ∧ ∃ x, G.Inc e x ∧ x ≠ v :=
  ⟨fun h ↦ ⟨h.inc, h.exists_inc_ne⟩, fun ⟨h, _, hex, hxv⟩ ↦ h.isLoopAt_or_isNonloopAt.elim
    (fun h' ↦ (hxv <| h'.eq_of_inc hex).elim) id⟩

lemma inc_eq_inc_iff {G' : Graph α β} : G.Inc e = G'.Inc e ↔ G.incFun e = G'.incFun e := by
  constructor <;> rintro h <;> ext x
  · obtain h0 | h1 | h2 := G'.incFun_eq_zero_or_one_or_two e x
    · rwa [h0, G.incFun_eq_zero, h, ← G'.incFun_eq_zero]
    · simp_rw [h1, G.incFun_eq_one, isNonloopAt_iff, h, ← isNonloopAt_iff]
      rwa [← G'.incFun_eq_one]
    simp_rw [h2, G.incFun_eq_two, isLoopAt_iff, h, ← isLoopAt_iff]
    rwa [← G'.incFun_eq_two]
  · unfold Inc
    rw [h]

/-- Two graphs with the same incidences are the same. -/
lemma ext_inc {G G' : Graph α β} (hV : G.V = G'.V) (hE : G.E = G'.E)
    (h : ∀ e x, G.Inc e x ↔ G'.Inc e x) : G = G' := by
  ext e x
  · rw [hV]
  · rw [hE]
  · congr 1
    rw [← inc_eq_inc_iff (G := G) (G' := G') (e := e)]
    ext x
    exact h e x

lemma exists_vertex_inc (G : Graph α β) (he : e ∈ G.E) : ∃ v, G.Inc e v := by
  unfold Inc
  by_contra! h
  have : (G.incFun e).sum (fun _ x ↦ x) = 0 := by
    unfold Finsupp.sum
    exact Finset.sum_eq_zero fun x a ↦ h x
  have := G.sum_eq he
  omega

-- def ofInc (V : Set α) (E : Set β) (Inc : α → β → Prop)
--     (vx_mem_of_inc : ∀ ⦃v e⦄, Inc v e → v ∈ V)
--     (edge_mem_of_inc : ∀ ⦃v e⦄, Inc v e → e ∈ E)
--     (exists_vertex_inc : ∀ ⦃e⦄, e ∈ E → ∃ v, Inc v e)
--     (not_hypergraph : ∀ ⦃x y z e⦄, Inc x e → Inc y e → Inc z e → x = y ∨ y = z ∨ x = z) :
--     Graph α β where
--   V := V
--   E := E
--   incFun e :=

section Degree

/-- The degree of a vertex as a term in `ℕ∞`. -/
noncomputable def eDegree (G : Graph α β) (v : α) : ℕ∞ := ∑' e, (G.incFun e v : ℕ∞)

/-- The degree of a vertex as a term in `ℕ` (with value zero if the degree is infinite). -/
noncomputable def degree (G : Graph α β) (v : α) : ℕ := (G.eDegree v).toNat

lemma degree_eq_fintype_sum [Fintype β] (G : Graph α β) (v : α) :
    G.degree v = ∑ e, G.incFun e v := by
  rw [degree, eDegree, tsum_eq_sum (s := Finset.univ) (by simp), ← Nat.cast_inj (R := ℕ∞),
    Nat.cast_sum, ENat.coe_toNat]
  refine WithTop.sum_ne_top.2 fun i _ ↦ ?_
  rw [← WithTop.lt_top_iff_ne_top]
  exact Batteries.compareOfLessAndEq_eq_lt.1 rfl

lemma degree_eq_finsum [Finite β] (G : Graph α β) (v : α) :
    G.degree v = ∑ᶠ e, G.incFun e v := by
  have := Fintype.ofFinite β
  rw [degree_eq_fintype_sum, finsum_eq_sum_of_fintype]

@[simp]
lemma finsum_incFun_eq (he : e ∈ G.E) : ∑ᶠ v, G.incFun e v = 2 := by
  rw [← G.sum_eq he, Finsupp.sum, finsum_eq_finset_sum_of_support_subset]
  simp

lemma handshake [Finite α] [Finite β] (G : Graph α β) :
    ∑ᶠ v, G.degree v = 2 * G.E.ncard := by
  have h := finsum_mem_comm (fun e v ↦ G.incFun e v) G.E.toFinite (Set.finite_univ (α := α))
  convert h.symm using 1
  · simp only [Set.mem_univ, finsum_true, degree_eq_finsum, finsum_mem_def]
    convert rfl with v e
    simp only [Set.indicator_apply_eq_self, incFun_eq_zero, not_imp_not]
    apply Inc.edge_mem
  simp only [Set.mem_univ, finsum_true]
  rw [finsum_mem_congr (show G.E = G.E from rfl) (fun x h ↦ finsum_incFun_eq h)]
  simp [mul_comm]

end Degree

section IsBetween

variable {u v : α}

def toMultiset (G : Graph α β) (e : β) : Multiset α := (G.incFun e).toMultiset

@[simp]
lemma mem_toMultiset_iff : u ∈ G.toMultiset e ↔ G.Inc e u := by
  simp only [toMultiset, mem_toMultiset, Inc.iff_mem_support, ne_eq, incFun_eq_zero, not_not]

lemma toMultiset_card (he : e ∈ G.E) : (G.toMultiset e).card = 2 := by
  simp only [toMultiset, card_toMultiset]
  exact G.sum_eq he

lemma toMultiset_count [DecidableEq α] (x : α) : (G.toMultiset e).count x = G.incFun e x := by
  rw [toMultiset, count_toMultiset]

noncomputable def toSym2 (G : Graph α β) {e : β} (he : e ∈ G.E) : Sym2 α :=
  Sym2.equivMultiset α |>.symm ⟨G.toMultiset e, toMultiset_card he⟩

lemma mem_toSym2_iff (he : e ∈ G.E) : x ∈ G.toSym2 he ↔ G.Inc e x := by
  simp only [toSym2, Sym2.mem_equivMultisetsymm_mem, mem_toMultiset_iff]

def IsBetween (G : Graph α β) (e : β) (x y : α) : Prop := {x, y} = G.toMultiset e

theorem IsBetween.symm (h : G.IsBetween e x y) : G.IsBetween e y x := by
  unfold IsBetween at h ⊢
  rw [← h]
  exact Multiset.pair_comm y x

lemma IsBetween.comm : G.IsBetween e x y ↔ G.IsBetween e y x := by
  refine ⟨IsBetween.symm, IsBetween.symm⟩

theorem IsBetween.inc_left (h : G.IsBetween e x y) : G.Inc e x := by
  rw [← mem_toMultiset_iff, ← h]
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, true_or]

theorem IsBetween.inc_right (h : G.IsBetween e x y) : G.Inc e y := h.symm.inc_left

lemma IsBetween.vx_mem_left (h : G.IsBetween e x y) : x ∈ G.V := h.inc_left.vx_mem

@[simp]
lemma not_isBetween_of_not_vx_mem_left (h : x ∉ G.V) : ¬ G.IsBetween e x y :=
  by_contra fun h' ↦ h <| (not_not.mp h').vx_mem_left

lemma IsBetween.vx_mem_right (h : G.IsBetween e x y) : y ∈ G.V := h.inc_right.vx_mem

@[simp]
lemma not_isBetween_of_not_vx_mem_right (h : y ∉ G.V) : ¬ G.IsBetween e x y :=
  by_contra fun h' ↦ h <| (not_not.mp h').vx_mem_right

lemma IsBetween.edge_mem (h : G.IsBetween e x y) : e ∈ G.E := h.inc_left.edge_mem

@[simp]
lemma not_isBetween_of_not_edge_mem (h : e ∉ G.E) : ¬ G.IsBetween e x y :=
  by_contra fun h' ↦ h <| (not_not.mp h').edge_mem

lemma IsBetween.inc_iff (hBtw : G.IsBetween e x y) : G.Inc e u ↔ u = x ∨ u = y := by
  constructor
  · rintro hinc
    rw [← mem_toMultiset_iff, ← hBtw] at hinc
    exact List.mem_pair.mp hinc
  · rintro (rfl | rfl)
    · exact hBtw.inc_left
    · exact hBtw.inc_right

@[simp]
lemma forall_inc_iff {P : α → Prop} (hbtw : G.IsBetween e x y):
    (∀ x, G.Inc e x → P x) ↔ P x ∧ P y := by
  constructor
  · rintro h
    use h x hbtw.inc_left, h y hbtw.inc_right
  · rintro ⟨hx, hy⟩ u hu
    obtain rfl | rfl := hbtw.inc_iff.mp hu <;> assumption

lemma IsBetween.pair_eq (h1 : G.IsBetween e x y) (h2 : G.IsBetween e u v) :
    ({x, y} : Multiset α) = {u, v} := by
  unfold IsBetween at h1 h2
  rwa [← h2] at h1

lemma IsBetween.toSym2_eq (h : G.IsBetween e x y) : G.toSym2 h.edge_mem = s(x, y) := by
  unfold IsBetween at h
  simp only [toSym2, ← h]
  rfl

lemma toSym2_eq_iff_IsBetween (he : e ∈ G.E) : G.toSym2 he = s(x, y) ↔ G.IsBetween e x y := by
  simp only [toSym2, Sym2.equivMultisetsymmEq_iff]
  rw [eq_comm]
  rfl

lemma IsBetween.sym2_eq (h1 : G.IsBetween e x y) (h2 : G.IsBetween e u v) :
    s(x, y) = s(u, v) := by
  rw [← h1.toSym2_eq, ← h2.toSym2_eq]

lemma IsBetween.eq_or_eq_of_IsBetween (h : G.IsBetween e x y) (h' : G.IsBetween e u v) :
    x = u ∧ y = v ∨ x = v ∧ y = u := by
  have := h.sym2_eq h'
  simpa using this

lemma inc_iff_exists_IsBetween : G.Inc e u ↔ ∃ v, G.IsBetween e u v := by
  by_cases he : e ∈ G.E
  · simp_rw [← mem_toSym2_iff he, ← toSym2_eq_iff_IsBetween he]
    exact Sym2.mem_iff_exists
  · simp [he]

lemma IsBetween.eq_of_IsBetween (h : G.IsBetween e x y) (h' : G.IsBetween e x u) : y = u := by
  obtain ⟨_h, rfl⟩ | ⟨rfl , rfl⟩ := h.eq_or_eq_of_IsBetween h' <;> rfl

@[simp]
lemma IsBetween.IsBetween_iff_eq_left (h : G.IsBetween e x y) : G.IsBetween e u y ↔ u = x :=
  ⟨fun h' => (h.symm.eq_of_IsBetween h'.symm).symm, fun h' => h' ▸ h⟩

@[simp]
lemma IsBetween.IsBetween_iff_eq_right (h : G.IsBetween e x y) : G.IsBetween e x u ↔ y = u :=
  ⟨fun h' => h.eq_of_IsBetween h', fun h' => h' ▸ h⟩

lemma IsLoopAt_iff_toMultiset_eq_replicate_two : G.IsLoopAt e x ↔
    G.toMultiset e = Multiset.replicate 2 x := by
  classical
  constructor <;> rintro h
  · have he : e ∈ G.E := h.edge_mem
    unfold IsLoopAt at h
    rw [← toMultiset_count x, ← toMultiset_card he, Multiset.count_eq_card] at h
    rw [Multiset.eq_replicate_card.mpr fun a b ↦ (h a b).symm, toMultiset_card he]
  · rw [IsLoopAt, ← toMultiset_count, h]
    simp

lemma IsLoopAt_iff_IsBetween : G.IsLoopAt e x ↔ G.IsBetween e x x := by
  rw [IsLoopAt_iff_toMultiset_eq_replicate_two, IsBetween, eq_comm]
  simp

@[simp]
lemma IsBetween.IsLoopAt_iff_eq (hbtw : G.IsBetween e x y) :
    G.IsLoopAt e x ↔ x = y := by
  rw [IsLoopAt_iff_IsBetween, hbtw.IsBetween_iff_eq_right, eq_comm]

lemma exist_IsBetween_of_mem (he : e ∈ G.E) : ∃ x y, G.IsBetween e x y := by
  simp_rw [← toSym2_eq_iff_IsBetween he]
  induction' G.toSym2 he with x y
  use x, y

lemma IsBetween_iff_inc_and_loop :
    G.IsBetween e x y ↔ G.Inc e x ∧ G.Inc e y ∧ (x = y → G.IsLoopAt e x) := by
  constructor
  · rintro h
    refine ⟨h.inc_left, h.inc_right, ?_⟩
    rintro rfl
    rw [h.IsLoopAt_iff_eq]
  · rintro ⟨hincx, hincy, hloop⟩
    by_cases h : x = y
    · subst y
      specialize hloop rfl
      exact IsLoopAt_iff_IsBetween.mp hloop
    · unfold IsBetween
      have : {x, y} ≤ G.toMultiset e := by
        rw [Multiset.le_iff_subset]
        · rintro z hz
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
          obtain rfl | rfl := hz <;> simpa
        · simpa
      refine Multiset.eq_of_le_of_card_le this ?_
      rw [toMultiset_card hincx.edge_mem]
      simp

lemma isBetween_eq_isBetween_iff_inc_eq_inc {G' : Graph α β} :
    G.IsBetween e = G'.IsBetween e ↔ G.Inc e = G'.Inc e := by
  constructor <;> rintro h
  · simp_rw [funext_iff, inc_iff_exists_IsBetween, eq_iff_iff]
    exact fun x => exists_congr (fun y => by rw [h])
  · ext x y
    rw [IsBetween_iff_inc_and_loop, IsBetween_iff_inc_and_loop, isLoopAt_iff, isLoopAt_iff, h]

lemma isBetween_eq_isBetween_iff {G' : Graph α β} :
    G.IsBetween e = G'.IsBetween e ↔ G.incFun e = G'.incFun e :=
  isBetween_eq_isBetween_iff_inc_eq_inc.trans inc_eq_inc_iff

lemma exist_IsBetween_of_mem_of_distinct {P : α → Prop} (hP1 : ∃ x, G.Inc e x ∧ P x)
    (hP2 : ∃ x, G.Inc e x ∧ ¬ P x) : ∃ x y, G.IsBetween e x y ∧ P x ∧ ¬ P y := by
  obtain ⟨x, hxinc, hx⟩ := hP1
  obtain ⟨y, hyinc, hy⟩ := hP2
  use x, y, ?_, hx, hy
  rw [IsBetween_iff_inc_and_loop]
  use hxinc, hyinc, ?_
  rintro rfl
  exact (hy hx).elim


noncomputable def ofIsBetween (V : Set α) (E : Set β) (isBtw : β → α → α → Prop)
    (hsymm : ∀ e x y, isBtw e x y → isBtw e y x)
    (vx_mem_of_isBtw_left : ∀ e x y, isBtw e x y → x ∈ V)
    (_edge_mem_of_isBtw : ∀ e x y, isBtw e x y → e ∈ E)
    (exists_vertex_isBtw : ∀ e, e ∈ E → ∃ x y, isBtw e x y)
    (_eq_of_isBtw : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → (x = u ∧ y = v) ∨ (x = v ∧ y = u))
    : Graph α β where
  V := V
  E := E
  incFun e := by
    classical
    by_cases he : e ∈ E
    · choose x y hbtw using exists_vertex_isBtw e he
      exact Multiset.toFinsupp {x, y}
    · exact 0
  sum_eq e he := by
    classical
    simp only [he, ↓reduceDIte]
    change (Multiset.toFinsupp _).sum (fun _ ↦ id) = 2
    rw [Multiset.toFinsupp_sum_eq]
    rfl
  vertex_support e v h := by
    by_cases he : e ∈ E
    · simp only [he, ↓reduceDIte, Multiset.insert_eq_cons, Multiset.toFinsupp_apply, ne_eq,
      Multiset.count_eq_zero, Multiset.mem_cons, Multiset.mem_singleton, not_and,
      not_not] at h
      obtain rfl | rfl := h
      · obtain ⟨y, hbtw⟩ := exists_vertex_isBtw e he |>.choose_spec
        refine vx_mem_of_isBtw_left e _ _ hbtw
      · obtain hbtw := exists_vertex_isBtw e he |>.choose_spec |>.choose_spec
        refine vx_mem_of_isBtw_left e _ _ (hsymm _ _ _ hbtw)
    · simp only [he, ↓reduceDIte, coe_zero, Pi.zero_apply, ne_eq, not_true_eq_false] at h
  edge_support e v h := by
    by_contra! he
    simp only [he, ↓reduceDIte, coe_zero, Pi.zero_apply, ne_eq, not_true_eq_false] at h

@[simp]
lemma IsBetween.ofIsBetween {V : Set α} {E : Set β} {isBtw : β → α → α → Prop}
    {hsymm : ∀ e x y, isBtw e x y → isBtw e y x}
    {vx_mem_of_isBtw_left : ∀ e x y, isBtw e x y → x ∈ V}
    {edge_mem_of_isBtw : ∀ e x y, isBtw e x y → e ∈ E}
    {exists_vertex_isBtw : ∀ e, e ∈ E → ∃ x y, isBtw e x y}
    {eq_of_isBtw : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → (x = u ∧ y = v) ∨ (x = v ∧ y = u)} :
    (ofIsBetween V E isBtw hsymm vx_mem_of_isBtw_left edge_mem_of_isBtw exists_vertex_isBtw eq_of_isBtw).IsBetween e x y ↔
      isBtw e x y := by
  unfold Graph.ofIsBetween
  simp only [IsBetween, toMultiset]
  by_cases he : e ∈ E
  · simp only [he, ↓reduceDIte, Multiset.toFinsupp_toMultiset]
    let u := (exists_vertex_isBtw e he).choose
    let v := (exists_vertex_isBtw e he).choose_spec.choose
    have huv : isBtw e u v := (exists_vertex_isBtw e he).choose_spec.choose_spec
    change ({x, y} : Multiset α) = {u, v} ↔ _
    rw [Multiset.pair_eq_pair_iff]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact huv
      · exact hsymm e _ _ huv
    · exact fun a ↦ eq_of_isBtw (hsymm e y x (hsymm e x y a)) huv
  · simp only [Multiset.insert_eq_cons, he, ↓reduceDIte, map_zero, Multiset.cons_ne_zero,
    false_iff]
    contrapose! he
    exact edge_mem_of_isBtw e y x (hsymm e x y (hsymm e y x (hsymm e x y he)))

@[simp]
lemma Inc.ofIsBetween {V : Set α} {E : Set β} {isBtw : β → α → α → Prop}
    {hsymm : ∀ e x y, isBtw e x y → isBtw e y x}
    {vx_mem_of_isBtw_left : ∀ e x y, isBtw e x y → x ∈ V}
    {edge_mem_of_isBtw : ∀ e x y, isBtw e x y → e ∈ E}
    {exists_vertex_isBtw : ∀ e, e ∈ E → ∃ x y, isBtw e x y}
    {eq_of_isBtw : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → (x = u ∧ y = v) ∨ (x = v ∧ y = u)} :
    (ofIsBetween V E isBtw hsymm vx_mem_of_isBtw_left edge_mem_of_isBtw exists_vertex_isBtw eq_of_isBtw).Inc e v ↔
      ∃ u, isBtw e v u := by
  simp_rw [inc_iff_exists_IsBetween, IsBetween.ofIsBetween]


def Adj (G : Graph α β) (x y : α) : Prop :=
  ∃ e, G.IsBetween e x y

lemma Adj.comm : G.Adj x y ↔ G.Adj y x := by
  unfold Adj
  constructor <;>
  · rintro ⟨e, h⟩
    exact ⟨e, h.symm⟩

lemma Adj.symm (h : G.Adj x y) : G.Adj y x := by
  obtain ⟨e, h⟩ := h
  exact ⟨e, h.symm⟩

@[simp]
lemma Adj.mem_left (h : G.Adj x y) : x ∈ G.V := by
  obtain ⟨e, hbtw⟩ := h
  exact hbtw.vx_mem_left

@[simp]
lemma Adj.mem_right (h : G.Adj x y) : y ∈ G.V := by
  rw [Adj.comm] at h
  exact Adj.mem_left h

@[simp]
lemma not_adj_of_not_mem_left (h : x ∉ G.V) : ¬G.Adj x y := by
  rintro ⟨e, hbtw⟩
  exact h hbtw.vx_mem_left

@[simp]
lemma not_adj_of_not_mem_right (h : y ∉ G.V) : ¬G.Adj x y := by
  rw [Adj.comm]
  exact not_adj_of_not_mem_left h

@[simp]
lemma IsBetween.Adj (h : G.IsBetween e x y) : G.Adj x y := by
  use e

def edgeNhd (G : Graph α β) (v : α) : Set β := {e | G.Inc e v}

def vxNhd (G : Graph α β) (v : α) : Set α := {x | G.Adj v x}




@[simp]
def reflAdj (G : Graph α β) (x y : α) :=
  G.Adj x y ∨ x = y ∧ x ∈ G.V

lemma reflAdj.of_vxMem (h : x ∈ G.V) : G.reflAdj x x := by
  simp only [reflAdj, h, and_self, or_true]

@[simp]
lemma reflAdj.refl (h : x ∈ G.V) : G.reflAdj x x := reflAdj.of_vxMem h

lemma reflAdj.symm (h : G.reflAdj x y) : G.reflAdj y x := by
  apply h.imp
  · exact fun h ↦ h.symm
  · rintro ⟨rfl, hx⟩
    exact ⟨rfl, hx⟩

lemma reflAdj.comm : G.reflAdj x y ↔ G.reflAdj y x := by
  refine ⟨reflAdj.symm, reflAdj.symm⟩

lemma Inc.reflAdj_of_inc (hx : G.Inc e x) (hy : G.Inc e y) : G.reflAdj x y := by
  by_cases hxy : x = y
  · subst y
    right
    exact ⟨rfl, hx.vx_mem⟩
  · left
    use e
    rw [IsBetween_iff_inc_and_loop]
    use hx, hy, fun h ↦ (hxy h).elim

@[simp]
lemma reflAdj.mem_left (h : G.reflAdj x y) : x ∈ G.V := by
  apply h.elim
  · exact fun a ↦ a.mem_left
  · tauto

@[simp]
lemma reflAdj.mem_right (h : G.reflAdj x y) : y ∈ G.V := by
  rw [reflAdj.comm] at h
  exact h.mem_left

@[simp]
lemma IsBetween.reflAdj (h : G.IsBetween e x y) : G.reflAdj x y := by
  left
  use e

@[simp]
lemma Adj.reflAdj (h : G.Adj x y) : G.reflAdj x y := by
  left
  exact h

lemma reflAdj.Adj_of_ne (h : G.reflAdj x y) (hne : x ≠ y) : G.Adj x y := by
  obtain ⟨e, h⟩ | ⟨rfl, hx⟩ := h
  · use e
  · contradiction

@[simp]
lemma reflAdj.Adj_iff_ne (hne : x ≠ y) : G.reflAdj x y ↔ G.Adj x y :=
  ⟨fun h => h.Adj_of_ne hne, fun h => h.reflAdj⟩

def Connected (G : Graph α β) := Relation.TransGen G.reflAdj

@[simp]
lemma IsBetween.connected (h : G.IsBetween e x y) : G.Connected x y :=
  Relation.TransGen.single h.reflAdj

@[simp]
lemma Adj.connected (h : G.Adj x y) : G.Connected x y := Relation.TransGen.single h.reflAdj

@[simp]
lemma reflAdj.connected (h : G.reflAdj x y) : G.Connected x y := Relation.TransGen.single h

lemma connected_self (hx : x ∈ G.V) : G.Connected x x :=
  Relation.TransGen.single <| reflAdj.of_vxMem hx

lemma Inc.connected_of_inc (hx : G.Inc e x) (hy : G.Inc e y) : G.Connected x y :=
  reflAdj.connected (hx.reflAdj_of_inc hy)

lemma Connected.comm : G.Connected x y ↔ G.Connected y x := by
  unfold Connected
  rw [Relation.transGen_swap]
  congr! 1
  ext
  exact reflAdj.comm

@[simp]
lemma Connected.refl {G : Graph α β} {x : α} (hx : x ∈ G.V) : G.Connected x x :=
  connected_self hx

lemma Connected.symm (h : G.Connected x y) : G.Connected y x := by
  rwa [Connected.comm]

instance : IsSymm α (G.Connected) := ⟨fun _ _ ↦ Connected.symm⟩

lemma Connected.trans {G : Graph α β} {x y z : α} (hxy : G.Connected x y) (hyz : G.Connected y z) :
    G.Connected x z := Relation.TransGen.trans hxy hyz

instance : IsTrans α (G.Connected) := ⟨fun _ _ _ ↦ Connected.trans⟩

@[simp]
lemma Connected.mem_left (hconn : G.Connected x y) : x ∈ G.V := by
  simp only [Connected, Relation.TransGen.head'_iff, not_exists, not_and, not_or] at hconn
  obtain ⟨a, hradj, hTG⟩ := hconn
  exact hradj.mem_left

@[simp]
lemma Connected.mem_right (hconn : G.Connected x y) : y ∈ G.V := by
  rw [Connected.comm] at hconn
  exact hconn.mem_left

@[simp]
lemma not_connected_of_not_mem (h : x ∉ G.V) : ¬G.Connected x y := by
  contrapose! h
  exact h.mem_left

@[simp]
lemma not_connected_of_not_mem' (h : y ∉ G.V) : ¬G.Connected x y := by
  rw [Connected.comm]
  exact not_connected_of_not_mem h

@[simp]
lemma Connected.refl_iff {G : Graph α β} {x : α} : G.Connected x x ↔ x ∈ G.V := by
  refine ⟨?_, Connected.refl⟩
  rintro h
  exact h.mem_left

class Conn (G : Graph α β) : Prop where
  all_conn : ∃ x, ∀ y ∈ G.V, G.Connected x y

end IsBetween
