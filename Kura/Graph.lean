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
  Inc₂ : β → α → α → Prop
  symm : ∀ ⦃e x y⦄, Inc₂ e x y → Inc₂ e y x
  vx_mem_left : ∀ ⦃e x y⦄, Inc₂ e x y → x ∈ V
  edge_mem : ∀ ⦃e x y⦄, Inc₂ e x y → e ∈ E
  exists_vx_inc₂ : ∀ ⦃e⦄, e ∈ E → ∃ x y, Inc₂ e x y
  left_eq_of_inc₂ : ∀ ⦃x y u v e⦄, Inc₂ e x y → Inc₂ e u v → x = u ∨ x = v

variable {α α' β β' : Type*} {G G' H H' : Graph α β} {x y z u v w : α} {e f : β} {S S' T T' : Set α}
  {F F' R R' : Set β}

namespace Graph

protected class Finite (G : Graph α β) : Prop where
  vx_fin : G.V.Finite
  edge_fin : G.E.Finite

instance instvxFinite [G.Finite] : G.V.Finite := Finite.vx_fin

instance instedgeFinite [G.Finite] : G.E.Finite := Finite.edge_fin

/- Definitions -/
-- This is now part of the definition of `Graph`.
-- def Inc₂ (G : Graph α β) (e : β) (x y : α) : Prop := {x, y} = G.toMultiset e

noncomputable def toMultiset (G : Graph α β) (e : β) : Multiset α := by
  classical
  exact if he : e ∈ G.E
    then {G.exists_vx_inc₂ he |>.choose, G.exists_vx_inc₂ he |>.choose_spec.choose}
    else 0

noncomputable def toSym2 (G : Graph α β) (e : β) (he : e ∈ G.E) : Sym2 α :=
  s(G.exists_vx_inc₂ he |>.choose, G.exists_vx_inc₂ he |>.choose_spec.choose)

noncomputable def IncFun (G : Graph α β) (e : β) : α →₀ ℕ := by
  classical
  exact (G.toMultiset e).toFinsupp

def Inc (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, G.Inc₂ e x y

def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.Inc₂ e x x

def IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop := G.Inc e x ∧ ¬ G.IsLoopAt e x

-- This is now part of the definition of `Graph`.
-- def Inc₂ (G : Graph α β) (e : β) (x y : α) : Prop := {x, y} = G.toMultiset e

-- noncomputable def toMultiset (G : Graph α β) (e : β) : Multiset α := sorry

-- noncomputable def IncFun (G : Graph α β) (e : β) : α →₀ ℕ := sorry

-- def Inc (G : Graph α β) (e : β) (x : α) : Prop := sorry

-- def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := sorry

-- def IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop := sorry

section Inc₂

lemma Inc₂.symm (h : G.Inc₂ e x y) : G.Inc₂ e y x := G.symm h

lemma Inc₂.vx_mem_left (h : G.Inc₂ e x y) : x ∈ G.V := G.vx_mem_left h

lemma Inc₂.vx_mem_right (h : G.Inc₂ e x y) : y ∈ G.V := G.vx_mem_left h.symm

lemma Inc₂.edge_mem (h : G.Inc₂ e x y) : e ∈ G.E := G.edge_mem h

lemma Inc₂.exists_vx_inc₂ (he : e ∈ G.E) : ∃ u v, G.Inc₂ e u v := G.exists_vx_inc₂ he

lemma Inc₂.left_eq_of_inc₂ (h : G.Inc₂ e x y) (h' : G.Inc₂ e u v) : x = u ∨ x = v :=
  G.left_eq_of_inc₂ h h'



lemma Inc₂.right_eq_of_inc₂ (h : G.Inc₂ e x y) (h' : G.Inc₂ e u v) : y = u ∨ y = v :=
  G.left_eq_of_inc₂ h.symm h'

lemma Inc₂.comm : G.Inc₂ e x y ↔ G.Inc₂ e y x := ⟨Inc₂.symm, Inc₂.symm⟩

@[simp]
lemma Inc₂.inc₂_iff_eq_left (h : G.Inc₂ e x y) : G.Inc₂ e u y ↔ u = x := by
  refine ⟨fun h' => ?_, fun h' => h' ▸ h⟩
  obtain (rfl | rfl) := h.left_eq_of_inc₂ h'
  on_goal 2 => obtain (rfl | rfl) := h'.left_eq_of_inc₂ h
  all_goals rfl

@[simp]
lemma Inc₂.inc₂_iff_eq_right (h : G.Inc₂ e x y) : G.Inc₂ e x u ↔ y = u :=
  ⟨fun h' => (h.symm.inc₂_iff_eq_left.mp h'.symm).symm, fun h' => h' ▸ h⟩

lemma Inc₂.eq_of_inc₂ (h : G.Inc₂ e x y) (h' : G.Inc₂ e u v) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  obtain (rfl | rfl) := h.left_eq_of_inc₂ h'
  · obtain rfl | rfl := h.right_eq_of_inc₂ h'
    · rw [h'.inc₂_iff_eq_right] at h
      tauto
    · tauto
  · obtain rfl | rfl := h.symm.left_eq_of_inc₂ h'
    · tauto
    · rw [h'.inc₂_iff_eq_left] at h
      tauto

@[simp]
lemma not_inc₂_of_not_edge_mem (h : e ∉ G.E) : ¬ G.Inc₂ e x y :=
  by_contra fun h' ↦ h <| (not_not.mp h').edge_mem

lemma Inc₂.pair_eq (h1 : G.Inc₂ e x y) (h2 : G.Inc₂ e u v) :
    ({x, y} : Multiset α) = {u, v} := by
  rw [Multiset.pair_eq_pair_iff]
  exact h1.eq_of_inc₂ h2

lemma Inc₂.sym2_eq_iff (h : G.Inc₂ e x y) : G.Inc₂ e u v ↔ s(x, y) = s(u, v) := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  constructor
  · exact h.eq_of_inc₂
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact h
    · exact h.symm

end Inc₂

section Inc

@[simp]
lemma Inc.vx_mem (h : G.Inc e x) : x ∈ G.V := h.choose_spec.vx_mem_left

@[simp]
lemma Inc.edge_mem (h : G.Inc e x) : e ∈ G.E := h.choose_spec.edge_mem

@[simp]
lemma Inc.exists_vx_inc (he : e ∈ G.E) : ∃ x, G.Inc e x := G.exists_vx_inc₂ he

lemma Inc.not_hypergraph (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ y = z ∨ x = z := by
  obtain ⟨x', hx⟩ := hx
  obtain ⟨y', hy⟩ := hy
  obtain ⟨z', hz⟩ := hz
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hx.eq_of_inc₂ hy <;>
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hx.eq_of_inc₂ hz <;>
  tauto

@[simp]
lemma not_inc_of_not_vx_mem (h : x ∉ G.V) : ¬ G.Inc e x :=
  by_contra fun h' ↦ h <| (not_not.mp h').vx_mem

@[simp]
lemma not_inc_of_not_edge_mem (h : e ∉ G.E) : ¬ G.Inc e x :=
  by_contra fun h' ↦ h <| (not_not.mp h').edge_mem

lemma exists_vertex_inc (G : Graph α β) (he : e ∈ G.E) : ∃ v, G.Inc e v := Inc₂.exists_vx_inc₂ he

end Inc

section toMultiset

@[simp]
lemma toMultiset.vx_mem (hxe : x ∈ G.toMultiset e) : x ∈ G.V := by
  simp only [toMultiset] at hxe
  split_ifs at hxe with he
  · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hxe
    obtain rfl | rfl := hxe
    · exact (G.exists_vx_inc₂ he).choose_spec.choose_spec.vx_mem_left
    · exact (G.exists_vx_inc₂ he).choose_spec.choose_spec.vx_mem_right
  · exact (Multiset.not_mem_zero _ hxe).elim

@[simp]
lemma toMultiset.edge_mem (hxe : x ∈ G.toMultiset e) : e ∈ G.E := by
  simp only [toMultiset] at hxe
  split_ifs at hxe with he
  · exact (G.exists_vx_inc₂ he).choose_spec.choose_spec.edge_mem
  · exact (Multiset.not_mem_zero _ hxe).elim

@[simp]
lemma toMultiset.card_eq_two (he : e ∈ G.E) : (G.toMultiset e).card = 2 := by
  simp only [toMultiset, he, ↓reduceDIte, Multiset.insert_eq_cons, Multiset.card_cons,
    Multiset.card_singleton, Nat.reduceAdd]

@[simp]
lemma toMultiset.eq_zero (he : e ∉ G.E) : G.toMultiset e = 0 := by
  simp only [toMultiset, he, ↓reduceDIte]



@[simp]
lemma toMultiset.edge_mem_of_mem (h : x ∈ G.toMultiset e) : e ∈ G.E := by
  simp only [toMultiset] at h
  split_ifs at h with he
  · exact (G.exists_vx_inc₂ he).choose_spec.choose_spec.edge_mem
  · exact (Multiset.not_mem_zero _ h).elim

@[simp]
lemma toMultiset_eq_zero_iff : G.toMultiset e = 0 ↔ e ∉ G.E := by
  refine ⟨fun h he ↦ ?_, toMultiset.eq_zero⟩
  have := h ▸ toMultiset.card_eq_two he
  simp at this

@[simp]
lemma toMultiset_card_eq_two_iff : (G.toMultiset e).card = 2 ↔ e ∈ G.E := by
  refine ⟨fun h ↦ ?_, fun he ↦ ?_⟩
  · rw [Multiset.card_eq_two] at h
    obtain ⟨x, y, hxy⟩ := h
    exact toMultiset.edge_mem (by rw [hxy]; simp : x ∈ G.toMultiset e)
  · rw [toMultiset.card_eq_two he]

lemma toMultiset_card_or : (G.toMultiset e).card = 2 ∨ (G.toMultiset e).card = 0 := by
  by_cases he : e ∈ G.E
  · exact Or.inl (toMultiset_card_eq_two_iff.mpr he)
  · exact Or.inr (Multiset.card_eq_zero.mpr (toMultiset_eq_zero_iff.mpr he))

end toMultiset

section toSym2

@[simp]
lemma toSym2.vx_mem (he : e ∈ G.E) (h : x ∈ G.toSym2 e he) : x ∈ G.V := by
  simp [toSym2] at h
  have := (Inc₂.exists_vx_inc₂ he).choose_spec.choose_spec
  obtain rfl | rfl := h
  · exact this.vx_mem_left
  · exact this.vx_mem_right

@[simp]
lemma toSym2.eq_iff_inc₂ (he : e ∈ G.E) : G.toSym2 e he = s(x, y) ↔ G.Inc₂ e x y := by
  constructor
  · rintro h
    have := (Inc₂.exists_vx_inc₂ he).choose_spec.choose_spec
    simp only [toSym2, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
    · exact this
    · exact this.symm
  · rintro h
    simp only [toSym2, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    exact (Inc₂.exists_vx_inc₂ he).choose_spec.choose_spec.eq_of_inc₂ h

end toSym2

section IncFun

@[simp]
lemma IncFun.sum_eq (he : e ∈ G.E) : (G.IncFun e).sum (fun _ ↦ id) = 2 := by
  classical
  simp only [IncFun]
  rw [Multiset.toFinsupp_sum_eq]
  exact toMultiset.card_eq_two he

@[simp]
lemma IncFun.vx_mem (hinc : G.IncFun e v ≠ 0) : v ∈ G.V := by
  classical
  simp only [IncFun] at hinc
  rw [← Finsupp.mem_support_iff, Multiset.toFinsupp_support, Multiset.mem_toFinset] at hinc
  exact toMultiset.vx_mem hinc

@[simp]
lemma IncFun.edge_mem (hinc : G.IncFun e v ≠ 0) : e ∈ G.E := by
  classical
  simp only [IncFun] at hinc
  rw [← Finsupp.mem_support_iff, Multiset.toFinsupp_support, Multiset.mem_toFinset] at hinc
  exact toMultiset.edge_mem hinc


@[simp]
lemma IncFun.eq_zero_of_edge_not_mem (he : e ∉ G.E) : G.IncFun e = 0 := by
  ext v
  contrapose! he
  exact IncFun.edge_mem he

@[simp]
lemma IncFun.eq_zero_of_vertex_not_mem (hv : v ∉ G.V) : G.IncFun e v = 0 := by
  contrapose! hv
  exact IncFun.vx_mem hv

@[simp]
lemma incFun_le_two (G : Graph α β) (e) (v) : G.IncFun e v ≤ 2 := by
  refine (em (G.IncFun e v ≠ 0)).elim (fun h ↦ ?_) (fun h ↦ by simp only [(not_not.mp h), zero_le])
  rw [← IncFun.sum_eq (IncFun.edge_mem h), Finsupp.sum]
  exact Finset.single_le_sum (by simp) (by simpa)

@[simp]
lemma incFun_eq_zero_or_one_or_two (G : Graph α β) (e : β) (v : α) :
    G.IncFun e v = 0 ∨ G.IncFun e v = 1 ∨ G.IncFun e v = 2 := by
  have h := incFun_le_two G e v
  interval_cases G.IncFun e v <;> tauto

end IncFun

-- Inc & Inc₂

lemma inc_iff_exists_inc₂ : G.Inc e x ↔ ∃ y, G.Inc₂ e x y := Iff.rfl

@[simp]
lemma Inc₂.inc_left (h : G.Inc₂ e x y) : G.Inc e x := by
  rw [inc_iff_exists_inc₂]
  use y, h

@[simp]
lemma Inc₂.inc_right (h : G.Inc₂ e x y) : G.Inc e y := by
  rw [inc_iff_exists_inc₂]
  use x, h.symm

@[simp]
lemma Inc₂.eq_of_inc (h₂ : G.Inc₂ e x y) (h : G.Inc e u) : x = u ∨ y = u := by
  obtain ⟨v, hv⟩ := h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h₂.eq_of_inc₂ hv <;> tauto

lemma inc₂_iff_inc_and_loop : G.Inc₂ e x y ↔ G.Inc e x ∧ G.Inc e y ∧ (x = y → G.IsLoopAt e x) := by
  constructor
  · refine fun h => ⟨h.inc_left, h.inc_right, ?_⟩
    rintro rfl
    exact h
  · rintro ⟨hincx, hincy, hloop⟩
    by_cases h : x = y
    · subst h
      exact hloop rfl
    · obtain ⟨x', hx'⟩ := hincx
      obtain ⟨y', hy'⟩ := hincy
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hx'.eq_of_inc₂ hy'
      · exact hloop rfl
      · exact hx'

lemma Inc₂.inc_iff (hBtw : G.Inc₂ e x y) : G.Inc e u ↔ x = u ∨ y = u := by
  constructor
  · rintro hinc
    exact hBtw.eq_of_inc hinc
  · rintro (rfl | rfl)
    · exact hBtw.inc_left
    · exact hBtw.inc_right

@[simp]
lemma Inc₂.forall_inc_iff {P : α → Prop} (hbtw : G.Inc₂ e x y) :
    (∀ x, G.Inc e x → P x) ↔ P x ∧ P y := by
  constructor
  · rintro h
    use h x hbtw.inc_left, h y hbtw.inc_right
  · rintro ⟨hx, hy⟩ u hu
    obtain rfl | rfl := hbtw.inc_iff.mp hu <;> assumption

@[simp]
lemma forall_inc_iff {P : α → Prop} (hbtw : G.Inc₂ e x y): (∀ x, G.Inc e x → P x) ↔ P x ∧ P y := by
  constructor
  · rintro h
    use h x hbtw.inc_left, h y hbtw.inc_right
  · rintro ⟨hx, hy⟩ u hu
    obtain rfl | rfl := hbtw.inc_iff.mp hu <;> assumption

-- Inc₂ & toMultiset

@[simp]
lemma toMultiset.Inc₂_of_edge_mem (h : G.toMultiset e = {x, y}) : G.Inc₂ e x y := by
  have he := toMultiset.edge_mem (by rw [h]; simp : x ∈ G.toMultiset e)
  simp only [toMultiset, he, ↓reduceDIte] at h
  rw [Multiset.pair_eq_pair_iff] at h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
  · exact (G.exists_vx_inc₂ he).choose_spec.choose_spec
  · exact (G.exists_vx_inc₂ he).choose_spec.choose_spec.symm

@[simp]
lemma Inc₂.toMultiset (h : G.Inc₂ e x y) : G.toMultiset e = {x, y} := by
  simp only [Graph.toMultiset, h.edge_mem, ↓reduceDIte]
  let u := (Inc₂.exists_vx_inc₂ h.edge_mem).choose
  let v := (Inc₂.exists_vx_inc₂ h.edge_mem).choose_spec.choose
  let huv : G.Inc₂ e u v := (Inc₂.exists_vx_inc₂ h.edge_mem).choose_spec.choose_spec
  change {u, v} = ({x, y} : Multiset α)
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := huv.eq_of_inc₂ h <;> rw [h1, h2]
  rw [Multiset.pair_comm]

lemma inc₂_iff_toMultiset : G.Inc₂ e x y ↔ G.toMultiset e = {x, y} :=
  ⟨Inc₂.toMultiset, toMultiset.Inc₂_of_edge_mem⟩

-- Inc & toMultiset

@[simp]
lemma inc_iff_mem_toMultiset : x ∈ G.toMultiset e ↔ G.Inc e x := by
  constructor
  · rintro h
    obtain ⟨u, v, huv⟩ := G.exists_vx_inc₂ (toMultiset.edge_mem_of_mem h)
    rw [inc₂_iff_toMultiset.mp huv] at h
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h
    obtain rfl | rfl := h
    · exact huv.inc_left
    · exact huv.inc_right
  · rintro ⟨y, h⟩
    rw [inc₂_iff_toMultiset.mp h]
    simp

alias ⟨toMultiset.Inc_of_mem, Inc.mem_toMultiset⟩ := inc_iff_mem_toMultiset

-- toMultiset & IncFun

@[simp]
lemma toMultiset_count [DecidableEq α] (x : α) : (G.toMultiset e).count x = G.IncFun e x := by
  classical
  by_cases he : e ∈ G.E
  · simp only [toMultiset, he, ↓reduceDIte, IncFun]
    convert (Multiset.toFinsupp_apply _ x).symm
  · simp only [toMultiset, he, ↓reduceDIte, Multiset.not_mem_zero, not_false_eq_true,
    Multiset.count_eq_zero_of_not_mem, IncFun, map_zero, coe_zero, Pi.zero_apply]

-- IncFun & Inc

@[simp]
lemma incFun_ne_zero : G.IncFun e v ≠ 0 ↔ G.Inc e v := by
  classical
  rw [← toMultiset_count, Multiset.count_ne_zero, inc_iff_mem_toMultiset]

@[simp]
lemma incFun_eq_zero : G.IncFun e x = 0 ↔ ¬ G.Inc e x := by
  rw [← incFun_ne_zero, not_not]

lemma Inc.iff_mem_support : G.Inc e x ↔ x ∈ (G.IncFun e).support := by
  rw [Finsupp.mem_support_iff, incFun_ne_zero]


section IsLoopAt

@[simp]
lemma IsLoopAt.vx_mem (h : G.IsLoopAt e v) : v ∈ G.V := h.vx_mem_left

@[simp]
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e v) : e ∈ G.E := Inc₂.edge_mem h

@[simp]
lemma IsNonloopAt.vx_mem (h : G.IsNonloopAt e v) : v ∈ G.V := h.left.vx_mem

@[simp]
lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e v) : e ∈ G.E := h.left.edge_mem

@[simp]
lemma IsLoopAt.inc (h : G.IsLoopAt e v) : G.Inc e v := by
  rw [IsLoopAt] at h
  exact h.inc_left

@[simp]
lemma IsNonloopAt.inc (h : G.IsNonloopAt e v) : G.Inc e v := h.left

lemma inc₂_eq_iff_isLoopAt : G.Inc₂ e x x ↔ G.IsLoopAt e x := Iff.rfl

alias ⟨Inc₂.IsLoopAt, IsLoopAt.inc₂⟩ := inc₂_eq_iff_isLoopAt

@[simp]
lemma Inc₂.IsLoopAt_iff_eq (hbtw : G.Inc₂ e x y) : G.IsLoopAt e x ↔ x = y := by
  rw [← inc₂_eq_iff_isLoopAt, hbtw.inc₂_iff_eq_right, eq_comm]

@[simp]
lemma inc_and_not_isLoopAt_iff_isNonloopAt :
    G.Inc e x ∧ ¬ G.IsLoopAt e x ↔ G.IsNonloopAt e x := Iff.rfl

alias ⟨_, IsNonloopAt.inc_and_not_isLoopAt⟩ := inc_and_not_isLoopAt_iff_isNonloopAt

@[simp]
lemma toMultiset_eq_replicate_two_iff_isLoopAt :
    G.toMultiset e = {x, x} ↔ G.IsLoopAt e x := by
  rw [← inc₂_eq_iff_isLoopAt]
  convert inc₂_iff_toMultiset.symm

@[simp]
lemma incFun_eq_two_iff_isLoopAt : G.IncFun e v = 2 ↔ G.IsLoopAt e v := by
  classical
  constructor
  · rintro h
    have he : e ∈ G.E := by
      apply IncFun.edge_mem
      rw [h]
      omega
    rw [← toMultiset.card_eq_two he, ← toMultiset_count, Multiset.count_eq_card] at h
    have := Multiset.eq_replicate_of_mem (fun a b ↦ (h a b).symm)
    rw [toMultiset.card_eq_two he] at this
    rwa [← inc₂_eq_iff_isLoopAt, inc₂_iff_toMultiset]
  · rintro h
    rw [← inc₂_eq_iff_isLoopAt, inc₂_iff_toMultiset] at h
    rw [← toMultiset_count, h]
    simp

@[simp]
lemma incFun_eq_one_iff_isNonloopAt : G.IncFun e x = 1 ↔ G.IsNonloopAt e x := by
  classical
  rw [le_antisymm_iff, and_comm, IsNonloopAt]
  refine Iff.and ?_ ?_
  · rw [← incFun_ne_zero]
    omega
  · rw [← incFun_eq_two_iff_isLoopAt]
    have : G.IncFun e x ≤ 2 := incFun_le_two G e x
    omega

lemma inc_iff_isLoopAt_or_isNonloopAt : G.Inc e v ↔ G.IsLoopAt e v ∨ G.IsNonloopAt e v := by
  rw [← incFun_ne_zero, ← incFun_eq_two_iff_isLoopAt, ← incFun_eq_one_iff_isNonloopAt]
  have h := G.incFun_le_two e v
  omega

alias ⟨Inc.isLoopAt_or_isNonloopAt, _⟩ := inc_iff_isLoopAt_or_isNonloopAt

lemma isLoopAt_iff : G.IsLoopAt e v ↔ G.Inc e v ∧ ∀ x, G.Inc e x → x = v := by
  classical
  wlog hev : G.Inc e v
  · exact iff_of_false (fun h ↦ hev h.inc) (by simp only [hev, false_and, not_false_eq_true])
  rw [← incFun_eq_two_iff_isLoopAt, ← IncFun.sum_eq hev.edge_mem, Finsupp.sum,
    Finset.sum_eq_sum_diff_singleton_add (i := v) (by simpa only [Finsupp.mem_support_iff, ne_eq,
      incFun_eq_zero, Decidable.not_not])]
  aesop

lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e v) (h_inc : G.Inc e x) : x = v :=
  (isLoopAt_iff.1 h).2 _ h_inc

@[simp]
lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e v) : ¬ G.IsLoopAt e v := by
  rw [← incFun_eq_one_iff_isNonloopAt] at h
  simp only [← incFun_eq_two_iff_isLoopAt, h, OfNat.one_ne_ofNat, not_false_eq_true]

@[simp]
lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e v) : ¬ G.IsNonloopAt e v := by
  rw [← incFun_eq_two_iff_isLoopAt] at h
  simp only [← incFun_eq_one_iff_isNonloopAt, h, OfNat.ofNat_ne_one, not_false_eq_true]

lemma IsNonloopAt.exists_inc_ne (h : G.IsNonloopAt e v) : ∃ w, G.Inc e w ∧ w ≠ v := by
  simpa [ne_eq, isLoopAt_iff, and_iff_right h.inc, not_forall, Classical.not_imp] using
    h.not_isLoopAt

lemma isNonloopAt_iff : G.IsNonloopAt e v ↔ G.Inc e v ∧ ∃ x, G.Inc e x ∧ x ≠ v :=
  ⟨fun h ↦ ⟨h.inc, h.exists_inc_ne⟩, fun ⟨h, _, hex, hxv⟩ ↦ h.isLoopAt_or_isNonloopAt.elim
    (fun h' ↦ (hxv <| h'.eq_of_inc hex).elim) id⟩

end IsLoopAt

section Adj

def Adj (G : Graph α β) (x y : α) : Prop := ∃ e, G.Inc₂ e x y

lemma Adj.comm : G.Adj x y ↔ G.Adj y x := by
  unfold Adj
  constructor <;>
  · rintro ⟨e, h⟩
    exact ⟨e, h.symm⟩

lemma Adj.symm (h : G.Adj x y) : G.Adj y x := Adj.comm.mp h

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

def edgeNhd (G : Graph α β) (v : α) : Set β := {e | G.Inc e v}

def vxNhd (G : Graph α β) (v : α) : Set α := {x | G.Adj v x}

end Adj

-- lemma inc_eq_inc_of_inc₂_le_inc₂ (h : G.Inc₂ ≤ G'.Inc₂) (he : e ∈ G.E) : G.Inc e = G'.Inc e := by
--   ext x
--   constructor
--   · rw [inc_iff_exists_inc₂, inc_iff_exists_inc₂]
--     rintro ⟨y, hbtw⟩
--     exact ⟨y, h _ _ _ hbtw⟩
--   · rintro hinc
--     obtain ⟨y, z, hbtw⟩ := G.exist_inc₂_of_mem he
--     obtain rfl | rfl := (h e y z hbtw).inc_iff.mp hinc
--     · exact hbtw.inc_left
--     · exact hbtw.inc_right

-- lemma incFun_eq_incFun_of_inc₂_le_inc₂ (h : G.Inc₂ ≤ G'.Inc₂) (he : e ∈ G.E) :
--     G.incFun e = G'.incFun e := by
--   rw [← inc_eq_inc_iff]
--   exact inc_eq_inc_of_inc₂_le_inc₂ h he

-- lemma exist_Inc₂_of_mem_of_distinct {P : α → Prop} (hP1 : ∃ x, G.Inc e x ∧ P x)
--     (hP2 : ∃ x, G.Inc e x ∧ ¬ P x) : ∃ x y, G.Inc₂ e x y ∧ P x ∧ ¬ P y := by
--   obtain ⟨x, hxinc, hx⟩ := hP1
--   obtain ⟨y, hyinc, hy⟩ := hP2
--   use x, y, ?_, hx, hy
--   rw [inc₂_iff_inc_and_loop]
--   use hxinc, hyinc, ?_
--   rintro rfl
--   exact (hy hx).elim
