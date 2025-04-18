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

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v w : α} {e f : β} {S S' T T' : Set α}
  {F F' R R' : Set β}

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

lemma inc_eq_inc_iff : G.Inc e = G'.Inc e ↔ G.incFun e = G'.incFun e := by
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
lemma ext_inc (hV : G.V = G'.V) (hE : G.E = G'.E)
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

section Inc₂
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

def Inc₂ (G : Graph α β) (e : β) (x y : α) : Prop := {x, y} = G.toMultiset e

theorem Inc₂.symm (h : G.Inc₂ e x y) : G.Inc₂ e y x := by
  unfold Inc₂ at h ⊢
  rw [← h]
  exact Multiset.pair_comm y x

lemma Inc₂.comm : G.Inc₂ e x y ↔ G.Inc₂ e y x := by
  refine ⟨Inc₂.symm, Inc₂.symm⟩

theorem Inc₂.inc_left (h : G.Inc₂ e x y) : G.Inc e x := by
  rw [← mem_toMultiset_iff, ← h]
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, true_or]

theorem Inc₂.inc_right (h : G.Inc₂ e x y) : G.Inc e y := h.symm.inc_left

lemma Inc₂.vx_mem_left (h : G.Inc₂ e x y) : x ∈ G.V := h.inc_left.vx_mem

@[simp]
lemma not_inc₂_of_not_vx_mem_left (h : x ∉ G.V) : ¬ G.Inc₂ e x y :=
  by_contra fun h' ↦ h <| (not_not.mp h').vx_mem_left

lemma Inc₂.vx_mem_right (h : G.Inc₂ e x y) : y ∈ G.V := h.inc_right.vx_mem

@[simp]
lemma not_inc₂_of_not_vx_mem_right (h : y ∉ G.V) : ¬ G.Inc₂ e x y :=
  by_contra fun h' ↦ h <| (not_not.mp h').vx_mem_right

lemma Inc₂.edge_mem (h : G.Inc₂ e x y) : e ∈ G.E := h.inc_left.edge_mem

@[simp]
lemma not_inc₂_of_not_edge_mem (h : e ∉ G.E) : ¬ G.Inc₂ e x y :=
  by_contra fun h' ↦ h <| (not_not.mp h').edge_mem

lemma Inc₂.inc_iff (hBtw : G.Inc₂ e x y) : G.Inc e u ↔ u = x ∨ u = y := by
  constructor
  · rintro hinc
    rw [← mem_toMultiset_iff, ← hBtw] at hinc
    exact List.mem_pair.mp hinc
  · rintro (rfl | rfl)
    · exact hBtw.inc_left
    · exact hBtw.inc_right

@[simp]
lemma forall_inc_iff {P : α → Prop} (hbtw : G.Inc₂ e x y): (∀ x, G.Inc e x → P x) ↔ P x ∧ P y := by
  constructor
  · rintro h
    use h x hbtw.inc_left, h y hbtw.inc_right
  · rintro ⟨hx, hy⟩ u hu
    obtain rfl | rfl := hbtw.inc_iff.mp hu <;> assumption

lemma Inc₂.pair_eq (h1 : G.Inc₂ e x y) (h2 : G.Inc₂ e u v) :
    ({x, y} : Multiset α) = {u, v} := by
  unfold Inc₂ at h1 h2
  rwa [← h2] at h1

lemma Inc₂.toSym2_eq (h : G.Inc₂ e x y) : G.toSym2 h.edge_mem = s(x, y) := by
  unfold Inc₂ at h
  simp only [toSym2, ← h]
  rfl

lemma toSym2_eq_iff_inc₂ (he : e ∈ G.E) : G.toSym2 he = s(x, y) ↔ G.Inc₂ e x y := by
  simp only [toSym2, Sym2.equivMultisetsymmEq_iff]
  rw [eq_comm]
  rfl

lemma Inc₂.sym2_eq (h1 : G.Inc₂ e x y) (h2 : G.Inc₂ e u v) : s(x, y) = s(u, v) := by
  rw [← h1.toSym2_eq, ← h2.toSym2_eq]

lemma Inc₂.eq_or_eq_of_inc₂ (h : G.Inc₂ e x y) (h' : G.Inc₂ e u v) :
    x = u ∧ y = v ∨ x = v ∧ y = u := by
  have := h.sym2_eq h'
  simpa using this

lemma inc_iff_exists_inc₂ : G.Inc e u ↔ ∃ v, G.Inc₂ e u v := by
  by_cases he : e ∈ G.E
  · simp_rw [← mem_toSym2_iff he, ← toSym2_eq_iff_inc₂ he]
    exact Sym2.mem_iff_exists
  · simp [he]

lemma Inc₂.eq_of_inc₂ (h : G.Inc₂ e x y) (h' : G.Inc₂ e x u) : y = u := by
  obtain ⟨_h, rfl⟩ | ⟨rfl , rfl⟩ := h.eq_or_eq_of_inc₂ h' <;> rfl

@[simp]
lemma Inc₂.inc₂_iff_eq_left (h : G.Inc₂ e x y) : G.Inc₂ e u y ↔ u = x :=
  ⟨fun h' => (h.symm.eq_of_inc₂ h'.symm).symm, fun h' => h' ▸ h⟩

@[simp]
lemma Inc₂.inc₂_iff_eq_right (h : G.Inc₂ e x y) : G.Inc₂ e x u ↔ y = u :=
  ⟨fun h' => h.eq_of_inc₂ h', fun h' => h' ▸ h⟩

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

lemma IsLoopAt_iff_inc₂ : G.IsLoopAt e x ↔ G.Inc₂ e x x := by
  rw [IsLoopAt_iff_toMultiset_eq_replicate_two, Inc₂, eq_comm]
  simp

@[simp]
lemma Inc₂.IsLoopAt_iff_eq (hbtw : G.Inc₂ e x y) : G.IsLoopAt e x ↔ x = y := by
  rw [IsLoopAt_iff_inc₂, hbtw.inc₂_iff_eq_right, eq_comm]

lemma exist_inc₂_of_mem (he : e ∈ G.E) : ∃ x y, G.Inc₂ e x y := by
  simp_rw [← toSym2_eq_iff_inc₂ he]
  induction' G.toSym2 he with x y
  use x, y

lemma inc₂_iff_inc_and_loop :
    G.Inc₂ e x y ↔ G.Inc e x ∧ G.Inc e y ∧ (x = y → G.IsLoopAt e x) := by
  constructor
  · rintro h
    refine ⟨h.inc_left, h.inc_right, ?_⟩
    rintro rfl
    rw [h.IsLoopAt_iff_eq]
  · rintro ⟨hincx, hincy, hloop⟩
    by_cases h : x = y
    · subst y
      specialize hloop rfl
      exact IsLoopAt_iff_inc₂.mp hloop
    · unfold Inc₂
      have : {x, y} ≤ G.toMultiset e := by
        rw [Multiset.le_iff_subset]
        · rintro z hz
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
          obtain rfl | rfl := hz <;> simpa
        · simpa
      refine Multiset.eq_of_le_of_card_le this ?_
      rw [toMultiset_card hincx.edge_mem]
      simp


lemma edge_subset_of_inc₂_le_inc₂ (h : G.Inc₂ ≤ G'.Inc₂) : G.E ⊆ G'.E := by
  rintro e he
  obtain ⟨x, y, hbtw⟩ := G.exist_inc₂_of_mem he
  exact (h e x y hbtw).edge_mem

lemma inc_eq_inc_of_inc₂_le_inc₂ (h : G.Inc₂ ≤ G'.Inc₂) (he : e ∈ G.E) : G.Inc e = G'.Inc e := by
  ext x
  constructor
  · rw [inc_iff_exists_inc₂, inc_iff_exists_inc₂]
    rintro ⟨y, hbtw⟩
    exact ⟨y, h _ _ _ hbtw⟩
  · rintro hinc
    obtain ⟨y, z, hbtw⟩ := G.exist_inc₂_of_mem he
    obtain rfl | rfl := (h e y z hbtw).inc_iff.mp hinc
    · exact hbtw.inc_left
    · exact hbtw.inc_right

lemma incFun_eq_incFun_of_inc₂_le_inc₂ (h : G.Inc₂ ≤ G'.Inc₂) (he : e ∈ G.E) :
    G.incFun e = G'.incFun e := by
  rw [← inc_eq_inc_iff]
  exact inc_eq_inc_of_inc₂_le_inc₂ h he

lemma inc₂_eq_inc₂_iff_inc_eq_inc : G.Inc₂ e = G'.Inc₂ e ↔ G.Inc e = G'.Inc e := by
  constructor <;> rintro h
  · simp_rw [funext_iff, inc_iff_exists_inc₂, eq_iff_iff]
    exact fun x => exists_congr (fun y => by rw [h])
  · ext x y
    rw [inc₂_iff_inc_and_loop, inc₂_iff_inc_and_loop, isLoopAt_iff, isLoopAt_iff, h]

lemma inc₂_eq_inc₂_iff : G.Inc₂ e = G'.Inc₂ e ↔ G.incFun e = G'.incFun e :=
  inc₂_eq_inc₂_iff_inc_eq_inc.trans inc_eq_inc_iff

lemma ext_Inc₂ (hV : G.V = G'.V) (h : ∀ e x y, G.Inc₂ e x y ↔ G'.Inc₂ e x y) : G = G' := by
  refine Graph.ext hV ((edge_subset_of_inc₂_le_inc₂ (h · · · |>.1)).antisymm
      (edge_subset_of_inc₂_le_inc₂ (h · · · |>.2))) ?_
  ext1 e
  rw [← inc₂_eq_inc₂_iff]
  ext x y
  exact h e x y

lemma exist_Inc₂_of_mem_of_distinct {P : α → Prop} (hP1 : ∃ x, G.Inc e x ∧ P x)
    (hP2 : ∃ x, G.Inc e x ∧ ¬ P x) : ∃ x y, G.Inc₂ e x y ∧ P x ∧ ¬ P y := by
  obtain ⟨x, hxinc, hx⟩ := hP1
  obtain ⟨y, hyinc, hy⟩ := hP2
  use x, y, ?_, hx, hy
  rw [inc₂_iff_inc_and_loop]
  use hxinc, hyinc, ?_
  rintro rfl
  exact (hy hx).elim

noncomputable def ofInc₂ (V : Set α) (E : Set β) (isBtw : β → α → α → Prop)
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
lemma Inc₂.ofInc₂ {V : Set α} {E : Set β} {isBtw : β → α → α → Prop}
    {hsymm : ∀ e x y, isBtw e x y → isBtw e y x}
    {vx_mem_of_isBtw_left : ∀ e x y, isBtw e x y → x ∈ V}
    {edge_mem_of_isBtw : ∀ e x y, isBtw e x y → e ∈ E}
    {exists_vertex_isBtw : ∀ e, e ∈ E → ∃ x y, isBtw e x y}
    {eq_of_isBtw : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → (x = u ∧ y = v) ∨ (x = v ∧ y = u)} :
    (ofInc₂ V E isBtw hsymm vx_mem_of_isBtw_left edge_mem_of_isBtw exists_vertex_isBtw eq_of_isBtw).Inc₂ e x y ↔
      isBtw e x y := by
  unfold Graph.ofInc₂
  simp only [Inc₂, toMultiset]
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
lemma Inc.ofInc₂ {V : Set α} {E : Set β} {isBtw : β → α → α → Prop}
    {hsymm : ∀ e x y, isBtw e x y → isBtw e y x}
    {vx_mem_of_isBtw_left : ∀ e x y, isBtw e x y → x ∈ V}
    {edge_mem_of_isBtw : ∀ e x y, isBtw e x y → e ∈ E}
    {exists_vertex_isBtw : ∀ e, e ∈ E → ∃ x y, isBtw e x y}
    {eq_of_isBtw : ∀ ⦃x y u v e⦄, isBtw e x y → isBtw e u v → (x = u ∧ y = v) ∨ (x = v ∧ y = u)} :
    (ofInc₂ V E isBtw hsymm vx_mem_of_isBtw_left edge_mem_of_isBtw exists_vertex_isBtw eq_of_isBtw).Inc e v ↔
      ∃ u, isBtw e v u := by
  simp_rw [inc_iff_exists_inc₂, Inc₂.ofInc₂]

end Inc₂

section SubgraphOrder
/-- Subgraph order of Graph -/
instance instPartialOrderGraph : PartialOrder (Graph α β) where
  le G₁ G₂ := G₁.V ≤ G₂.V ∧ G₁.Inc₂ ≤ G₂.Inc₂
  le_refl G := by simp only [subset_refl, le_refl, implies_true, exists_const, and_self]
  le_trans G₁ G₂ G₃ h₁₂ h₂₃ := by
    obtain ⟨h₁₂v, h₁₂S⟩ := h₁₂
    obtain ⟨h₂₃v, h₂₃S⟩ := h₂₃
    exact ⟨h₁₂v.trans h₂₃v, h₁₂S.trans h₂₃S⟩
  le_antisymm G₁ G₂ h₁₂ h₂₁ := ext_Inc₂ (h₁₂.1.antisymm h₂₁.1) fun e x y ↦ (by
    rw [h₁₂.2.antisymm h₂₁.2])

@[simp] lemma vx_subset_of_le (hle : G ≤ H) : G.V ⊆ H.V := hle.1

@[simp] lemma mem_of_le (hle : G ≤ H) : x ∈ G.V → x ∈ H.V := (hle.1 ·)

@[simp] lemma edge_subset_of_le (hle : G ≤ H) : G.E ⊆ H.E := edge_subset_of_inc₂_le_inc₂ hle.2

@[simp] lemma edge_mem_of_le (hle : G ≤ H) : e ∈ G.E → e ∈ H.E := (edge_subset_of_le hle ·)

lemma Inc_iff_Inc_of_le (hle : G ≤ H) (he : e ∈ G.E) : G.Inc e v ↔ H.Inc e v := by
  rw [inc_eq_inc_of_inc₂_le_inc₂ hle.2 he]

lemma incFun_eq_incFun_of_le (hle : G ≤ H) (he : e ∈ G.E) : G.incFun e = H.incFun e :=
  incFun_eq_incFun_of_inc₂_le_inc₂ hle.2 he

lemma Inc₂_iff_Inc₂_of_le (hle : G ≤ H) (he : e ∈ G.E) : G.Inc₂ e x y ↔ H.Inc₂ e x y := by
  suffices G.Inc₂ e = H.Inc₂ e by rw [this]
  rw [inc₂_eq_inc₂_iff]
  exact incFun_eq_incFun_of_le hle he

lemma le_of_exist_mutual_le (hle1 : G' ≤ H') (hle2 : H ≤ H') : G' ≤ H ↔ G'.V ⊆ H.V ∧ G'.E ⊆ H.E := by
  constructor
  · intro h
    exact ⟨vx_subset_of_le h, edge_subset_of_le h⟩
  · rintro ⟨hV, hE⟩
    refine ⟨hV, ?_⟩
    rintro e x y hbtw
    rwa [Inc₂_iff_Inc₂_of_le hle2 (hE hbtw.edge_mem), ← Inc₂_iff_Inc₂_of_le hle1 hbtw.edge_mem]

@[simp]
lemma Inc.le (hinc : G.Inc e x) (hle : G ≤ H) : H.Inc e x := by
  rwa [← Inc_iff_Inc_of_le hle hinc.edge_mem]

lemma IsLoopAt_iff_IsLoopAt_of_edge_mem_le (hle : G ≤ H) (he : e ∈ G.E) :
    G.IsLoopAt e x ↔ H.IsLoopAt e x := by
  unfold IsLoopAt
  rw [incFun_eq_incFun_of_le hle he]

lemma IsLoop.le (hisLoopAt : G.IsLoopAt e x) (hle : G ≤ H) : H.IsLoopAt e x := by
  rwa [← IsLoopAt_iff_IsLoopAt_of_edge_mem_le hle hisLoopAt.edge_mem]

lemma le_iff_inc : G ≤ H ↔ G.V ⊆ H.V ∧ G.E ⊆ H.E ∧ ∀ e ∈ G.E, ∀ v,
  G.Inc e v ↔ H.Inc e v := by
  constructor
  · rintro hle
    exact ⟨vx_subset_of_le hle, edge_subset_of_le hle, fun e he v ↦ Inc_iff_Inc_of_le hle he⟩
  · refine fun ⟨hV, hE, hinc⟩ ↦ ⟨hV, fun e x y ↦ ?_⟩
    by_cases he : e ∈ G.E
    · rw [inc₂_eq_inc₂_iff_inc_eq_inc.mpr (by ext; exact hinc e he _)]
    · simp [he]

-- This is now the definition of `le`
-- lemma le_iff_inc₂ : G ≤ H ↔ G.V ⊆ H.V ∧ G.E ⊆ H.E ∧ ∀ e ∈ G.E, ∀ v w,
--   G.Inc₂ e v w ↔ H.Inc₂ e v w := by
--   constructor
--   · rintro ⟨hV, hE, hinc⟩
--     refine ⟨hV, hE, fun e he v w ↦ ?_⟩
--     unfold Inc₂ toMultiset
--     rw [hinc e he]
--   · refine fun ⟨hV, hE, hinc⟩ ↦ ⟨hV, hE, fun e he ↦ ?_⟩
--     rw [← inc₂_eq_inc₂_iff]
--     ext v w
--     exact hinc e he v w

lemma inc₂_iff_inc₂_of_edge_mem_le (hle : G ≤ H) (he : e ∈ G.E) :
    G.Inc₂ e u v ↔ H.Inc₂ e u v := by
  unfold Inc₂ toMultiset
  rw [incFun_eq_incFun_of_le hle he]

lemma Inc₂.le (h : G.Inc₂ e u v) (hle : G ≤ H) : H.Inc₂ e u v := by
  rwa [← inc₂_iff_inc₂_of_edge_mem_le hle (edge_mem h)]

/-- If G₁ ≤ G₂ and G₂ is finite, then G₁ is finite too. -/
theorem finite_of_le_finite (hle : G ≤ H) [h : H.Finite] : G.Finite := by
  constructor
  · -- Prove the vertex set is finite
    apply Set.Finite.subset h.vx_fin
    exact vx_subset_of_le hle
  · -- Prove the edge set is finite
    apply Set.Finite.subset h.edge_fin
    exact edge_subset_of_le hle

lemma vx_ncard_le_of_le [hfin : H.Finite] (hle : G ≤ H) : G.V.ncard ≤ H.V.ncard :=
  Set.ncard_le_ncard (vx_subset_of_le hle) hfin.vx_fin

lemma edge_ncard_le_of_le [hfin : H.Finite] (hle : G ≤ H) : G.E.ncard ≤ H.E.ncard :=
  Set.ncard_le_ncard (edge_subset_of_le hle) hfin.edge_fin

end SubgraphOrder

section Adj

def Adj (G : Graph α β) (x y : α) : Prop :=
  ∃ e, G.Inc₂ e x y

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
lemma Inc₂.Adj (h : G.Inc₂ e x y) : G.Adj x y := by
  use e

lemma Adj.le (hadj : G.Adj u v) (hle : G ≤ H) : H.Adj u v := by
  obtain ⟨e, hbtw⟩ := hadj
  use e, hbtw.le hle

def edgeNhd (G : Graph α β) (v : α) : Set β := {e | G.Inc e v}

def vxNhd (G : Graph α β) (v : α) : Set α := {x | G.Adj v x}

end Adj

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
