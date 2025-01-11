import Mathlib.Data.List.Sym
import Mathlib.Data.List.DropRight


namespace List
variable {α : Type _}

@[simp]
lemma takeWhile_length_le (p : α → Bool) (l : List α) :
  (l.takeWhile p).length ≤ l.length := by
  induction l with
  | nil => simp only [takeWhile_nil, length_nil, le_refl]
  | cons a as ih => by_cases h : p a <;> simp_all only [decide_false, Bool.false_eq_true,
    not_false_eq_true, takeWhile_cons_of_neg, length_nil, length_cons, Nat.le_add_left,
    decide_true, takeWhile_cons_of_pos, Nat.add_le_add_iff_right]

lemma rtakeWhile_length_le_length (p : α → Bool) (l : List α) :
  (l.rtakeWhile p).length ≤ l.length := by
  unfold List.rtakeWhile
  rw [length_reverse]
  refine (l.reverse.takeWhile_length_le p).trans ?_
  simp only [length_reverse, le_refl]

lemma rtakeWhlie_cons (p : α → Bool) (a : α) (l : List α) (ha : ¬ p a):
  (a :: l).rtakeWhile p = l.rtakeWhile p := by
  simp only [List.rtakeWhile, reverse_cons, reverse_inj]
  sorry

lemma rdropWhile_append_rtakeWhile (p : α → Bool) (l : List α) :
  (l.rdropWhile p) ++ l.rtakeWhile p = l := by
  induction l with
  | nil => simp only [rdropWhile_nil, rtakeWhile_nil, append_nil]
  | cons a as ih =>
    simp only [rdropWhile, rtakeWhile]
    rw [← reverse_append, List.reverse_eq_iff]
    apply List.takeWhile_append_dropWhile



def skip [DecidableEq α] (l : List α) : List α :=
match l with
| [] => []
| a :: as => a :: skip (as.rtakeWhile (· != a))
termination_by l.length
decreasing_by
  simp only [length_cons, gt_iff_lt]
  suffices (as.rtakeWhile (· != a)).length ≤ as.length by omega
  exact rtakeWhile_length_le_length (· != a) as

@[simp]
lemma skip_nil [DecidableEq α] : ([] : List α).skip = [] := by
  unfold skip
  rfl

@[simp]
lemma skip_ne_nil [DecidableEq α] {l : List α} :
  l.skip ≠ [] ↔ l ≠ [] := by
  rw [not_iff_not]
  match l with
  | [] => simp only [skip_nil]
  | a :: as => simp only [skip, cons_ne_nil]

@[simp]
lemma skip_head? [DecidableEq α] (l : List α) : l.skip.head? = l.head? := by
  cases l
  · simp only [skip_nil, head?_nil]
  · simp only [skip, head?_cons]

@[simp]
lemma skip_getLast? [DecidableEq α] (l : List α) : l.skip.getLast? = l.getLast? := by
  induction' l using Nat.strongRecMeasure with l l ih
  exact l.length
  match l with
  | [] => simp only [skip_nil, length_nil, Nat.zero_le]
  | a :: as =>
    simp only [skip, getLast?_cons, Option.some.injEq]
    have := rtakeWhile_length_le_length (· != a) as
    rw [ih (as.rtakeWhile (· != a)) (by rw [length_cons]; omega)]
    by_cases h : as.rtakeWhile (· != a) = []
    · rw [h, getLast?_nil, Option.getD_none]
      by_cases h' : as = []
      · rw [h', getLast?_nil, Option.getD_none]
      · simp only [rtakeWhile_eq_nil_iff, ne_eq, h', not_false_eq_true, bne_iff_ne,
        getLast_eq_iff_getLast?_eq_some, Decidable.not_not, forall_const] at h
        rw [h, Option.getD_some]
    · have := (as.rtakeWhile_suffix _).ne_nil h
      rw [getLast?_eq_getLast_of_ne_nil h, Option.getD_some, getLast?_eq_getLast_of_ne_nil this]
      apply (as.rtakeWhile_suffix _).getLast

lemma skip_length_le [DecidableEq α] (l : List α) : (l.skip).length ≤ l.length := by
  induction' l using Nat.strongRecMeasure with l l ih
  exact l.length
  match l with
  | [] => simp only [skip_nil, length_nil, Nat.zero_le]
  | a :: as =>
    simp_all only [skip, length_cons, ge_iff_le]
    suffices (as.rtakeWhile (· != a)).skip.length ≤ as.length by omega
    have := rtakeWhile_length_le_length (· != a) as
    refine (ih (as.rtakeWhile (· != a)) (by omega)).trans this

lemma skip_sublist [DecidableEq α] (l : List α) : l.skip <+ l := by
  induction' l using Nat.strongRecMeasure with l l ih
  exact l.length
  match l with
  | [] => simp only [skip_nil, Sublist.refl]
  | a :: as =>
    simp only [skip, cons_sublist_cons]
    have := rtakeWhile_length_le_length (· != a) as
    refine (ih (as.rtakeWhile (· != a)) (by rw [length_cons]; omega)).trans ?_
    rw [List.rtakeWhile, ← List.sublist_reverse_iff]
    exact takeWhile_sublist (· != a)

lemma skip_nodup [DecidableEq α] (l : List α) : (l.skip).Nodup := by
  induction' l using Nat.strongRecMeasure with l l ih
  exact l.length
  match l with
  | [] => simp only [skip_nil, nodup_nil]
  | a :: as =>
    simp only [skip, nodup_cons]
    refine ⟨?_,?_⟩
    · rintro hmem
      have hmem := (takeWhile (fun x ↦ x != a) as.reverse).reverse.skip_sublist.mem hmem
      simp only [mem_reverse] at hmem
      have := List.mem_takeWhile_imp hmem
      simp only [bne_self_eq_false, Bool.false_eq_true] at this
    · have := rtakeWhile_length_le_length (· != a) as
      exact ih (as.rtakeWhile (· != a)) (by rw [length_cons]; omega)

lemma Chain'.skip [DecidableEq α] {r : α → α → Prop} {l : List α} (h : Chain' r l) :
  Chain' r l.skip := by
  induction l using Nat.strongRecMeasure with
  | f l => exact l.length
  | ind l ih =>
    match l with
    | [] => simp only [skip_nil, chain'_nil]
    | [a] => simp only [List.skip, rtakeWhile_nil, skip_nil, chain'_singleton]
    | a :: b :: as =>
      rw [List.chain'_cons', ← rdropWhile_append_rtakeWhile (· != a) (b :: as),
        List.chain'_append] at h
      obtain ⟨hhead, _hdw, htw, hbtw⟩ := h
      simp only [List.skip]
      rw [List.chain'_cons']
      refine ⟨?_,?_⟩
      · rintro c hc
        simp only [skip_head?] at hc
        by_cases h : (b :: as).rdropWhile (· != a) = []
        · have : (b :: as).rtakeWhile (· != a) = b :: as := by
            conv_rhs => rw [← rdropWhile_append_rtakeWhile (· != a) (b :: as)]
            exact self_eq_append_left.mpr h
          simp only [this, head?_cons, Option.some.injEq, h, nil_append, Option.mem_def,
            forall_eq'] at hc hhead
          subst hc
          exact hhead
        · refine hbtw a ?_ c hc
          have := List.rdropWhile_last_not _ _ h
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
          simpa only [getLast?_eq_getLast_of_ne_nil h, Option.mem_def, Option.some.injEq]
      · have := rtakeWhile_length_le_length (· != a) (b :: as)
        exact ih ((b :: as).rtakeWhile (· != a)) (by rw [length_cons]; omega) htw

lemma Chain.skip [DecidableEq α] {r : α → α → Prop} {a : α} {l : List α} (h : Chain r a l) :
  Chain r a l.skip := by
  change Chain' r (a :: l) at h
  change Chain' r (a :: l.skip)
  rw [List.chain'_cons'] at h
  apply Chain'.cons' (Chain'.skip h.2)
  intro b hb
  simp only [skip_head?] at hb
  exact h.1 b hb

theorem exists_nodup_chain'_of_relationReflTransGen [DecidableEq α] {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    ∃ l, ∃ (hl : l ≠ []), Chain' r l ∧ l.head hl = a ∧ getLast l hl = b ∧ l.Nodup := by
  obtain ⟨l, hr, hlast⟩ := List.exists_chain_of_relationReflTransGen h
  change Chain' r (a :: l) at hr
  refine ⟨(a :: l).skip, ?_, hr.skip, ?_, ?_, skip_nodup _⟩
  · simp only [ne_eq, skip_ne_nil, reduceCtorEq, not_false_eq_true]
  · simp only [skip, head_cons]
  · have := (a :: l).skip_getLast?
    rw [getLast?_eq_getLast_of_ne_nil (by simp), getLast?_eq_getLast_of_ne_nil (by simp),
      Option.some_inj] at this
    exact this ▸ hlast

theorem exists_nodup_chain_of_relationReflTransGen [DecidableEq α] {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    ∃ l, Chain r a l ∧ getLast (a :: l) (cons_ne_nil a l) = b ∧ (a :: l).Nodup := by
  obtain ⟨l, hl, hr, rfl, hlast, hnodup⟩ := exists_nodup_chain'_of_relationReflTransGen h
  refine ⟨l.tail, ?_, by simpa only [head_cons_tail], by rwa [head_cons_tail]⟩
  rw [← head_cons_tail _ hl] at hr
  simpa only [Chain'] using hr

lemma sizeOf_filter_le' (p : α → Bool) (s : List α) :
  sizeOf (s.filter p) ≤ sizeOf s := by
  match s with
  | [] => simp
  | a :: as =>
    by_cases h : p a
    · simp only [filter_cons_of_pos h, cons.sizeOf_spec, sizeOf_default, add_zero,
      Nat.add_le_add_iff_left, sizeOf_filter_le' p as]
    · simp only [filter_cons_of_neg h, cons.sizeOf_spec, sizeOf_default, add_zero]
      obtain := sizeOf_filter_le' p as
      omega

lemma sizeOf_filter_le (p : α → Prop) [DecidablePred p] (s : List α) :
  sizeOf (s.filter p) ≤ sizeOf s := sizeOf_filter_le' (fun b ↦ decide (p b)) s

lemma sizeOf_filter_lt' {p : α → Bool} (s : List α) {b : α} (hs : b ∈ s) (hp : ¬ p b) :
  sizeOf (s.filter p) < sizeOf s := by
  match s with
  | [] => simp only [not_mem_nil] at hs
  | a :: as =>
    by_cases h : p a
    · have : b ∈ as := by
        by_contra! has
        simp only [mem_cons, has, or_false] at hs
        subst hs
        exact hp h
      simp only [filter_cons_of_pos h, cons.sizeOf_spec, sizeOf_default, add_zero,
      Nat.add_lt_add_iff_left, gt_iff_lt]
      exact sizeOf_filter_lt' as this hp
    · simp only [filter_cons_of_neg h, cons.sizeOf_spec, sizeOf_default, add_zero]
      suffices sizeOf (as.filter p) ≤ sizeOf as by omega
      exact sizeOf_filter_le' p as

lemma sizeOf_filter_lt {p : α → Prop} [DecidablePred p] (s : List α) {b : α} (hs : b ∈ s) (hp : ¬ p b) :
  sizeOf (s.filter p) < sizeOf s := sizeOf_filter_lt' (p := fun b ↦ decide (p b)) s hs (by simp only [hp,
    decide_false, Bool.false_eq_true, not_false_eq_true])

lemma sizeOf_filter_le_filter' {p q : α → Bool} (hpq : ∀ a, p a → q a) (s : List α) :
  sizeOf (s.filter p) ≤ sizeOf (s.filter q) := by
  match s with
  | [] => simp only [filter_nil, nil.sizeOf_spec, le_refl]
  | a :: as =>
    by_cases hpa : p a <;> by_cases hqa : q a
    · simp [filter_cons_of_pos hpa, filter_cons_of_pos hqa, cons.sizeOf_spec, sizeOf_default,
      add_zero, sizeOf_filter_le_filter' hpq as]
    · exfalso
      exact hqa <| hpq a hpa
    · simp [filter_cons_of_neg hpa, filter_cons_of_pos hqa, cons.sizeOf_spec, sizeOf_default,
      add_zero]
      have := sizeOf_filter_le_filter' hpq as
      omega
    · simp [filter_cons_of_neg hpa, filter_cons_of_neg hqa, cons.sizeOf_spec, sizeOf_default,
      add_zero, sizeOf_filter_le_filter' hpq as]

lemma sizeOf_filter_le_filter {p q : α → Prop} [DecidablePred p] [DecidablePred q]
  (hpq : ∀ a, p a → q a) (s : List α) : sizeOf (s.filter p) ≤ sizeOf (s.filter q) :=
  sizeOf_filter_le_filter' (fun a h ↦ by simp_all only [decide_eq_true_eq, decide_true]) s

lemma sizeOf_filter_lt_filter' {p q : α → Bool} (hpq : ∀ a, p a → q a) (s : List α) {b : α}
  (hs : b ∈ s) (hp : ¬ p b) (hq : q b) :
  sizeOf (s.filter p) < sizeOf (s.filter q) := by
  match s with
  | [] => simp only [not_mem_nil] at hs
  | a :: as =>
    by_cases hpa : p a <;> by_cases hqa : q a
    · simp only [filter_cons_of_pos hpa, cons.sizeOf_spec, sizeOf_default, add_zero,
      filter_cons_of_pos hqa, Nat.add_lt_add_iff_left, gt_iff_lt]
      have : b ∈ as := by
        by_contra! has
        simp only [mem_cons, has, or_false] at hs
        subst hs
        exact hp hpa
      have := sizeOf_filter_lt_filter' hpq as this hp hq
      omega
    · simp only [filter_cons_of_pos hpa, filter_cons_of_neg hqa, cons.sizeOf_spec, sizeOf_default,
      add_zero]
      exfalso
      exact hqa <| hpq a hpa
    · simp only [filter_cons_of_neg hpa, filter_cons_of_pos hqa, cons.sizeOf_spec, sizeOf_default,
      add_zero]
      have := sizeOf_filter_le_filter' hpq as
      omega
    · simp only [filter_cons_of_neg hpa, filter_cons_of_neg hqa, cons.sizeOf_spec, sizeOf_default,
      add_zero]
      have : b ∈ as := by
        by_contra! has
        simp only [mem_cons, has, or_false] at hs
        subst hs
        exact hqa hq
      have := sizeOf_filter_lt_filter' hpq as this hp hq
      omega

lemma sizeOf_filter_lt_filter {p q : α → Prop} [DecidablePred p] [DecidablePred q]
  (hpq : ∀ a, p a → q a) (s : List α) {b : α} (hs : b ∈ s) (hp : ¬ p b) (hq : q b) :
  sizeOf (s.filter p) < sizeOf (s.filter q) :=
  sizeOf_filter_lt_filter' (fun a h ↦ by simp_all only [decide_eq_true_eq, decide_true]) s hs
    (by simpa only [decide_eq_true_eq]) (by simpa only [decide_eq_true_eq])

lemma not_mem_of_length_eq_zero {l : List α} {a : α} (h : l.length = 0) : a ∉ l := by
  intro h'
  rw [length_eq_zero] at h
  subst h
  simp only [not_mem_nil] at h'

@[simp]
theorem indexOf_eq_zero_iff [BEq α] [LawfulBEq α] {l : List α} (hl : l ≠ []) {a : α} :
    indexOf a l = 0 ↔ l.head hl = a := by
  match l, hl with
  | x :: xs, h =>
    simp only [indexOf, head_cons]
    rw [findIdx_cons]
    by_cases h' : x == a
    · simp only [h', cond_true, true_iff]
      exact beq_iff_eq.mp h'
    · simp only [h', cond_false, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
      false_iff, ne_eq]
      exact beq_iff_eq.not.mp h'

theorem getLast_tail_eq_getLast {l : List α} (h : l.tail ≠ []) :
    l.tail.getLast h = l.getLast (ne_nil_of_drop_ne_nil ((drop_one l).symm ▸ h)) := by
  match l with
  | [] => contradiction
  | a :: as =>
    rw [tail_cons] at h
    simp only [tail_cons, getLast_cons h]

theorem get_zero_eq_head_of_ne_nil {l : List α} (h : l ≠ []) :
    l.get ⟨ 0, length_pos_iff_ne_nil.mpr h ⟩ = l.head h := by
  match l with
  | [] => contradiction
  | a :: as => rfl

theorem head_reverse_of_ne_nil (l : List α) (hl : l ≠ []) :
    l.reverse.head ((not_congr List.reverse_eq_nil_iff).mpr hl) = l.getLast hl := by
  have : l.getLast hl = l.reverse.reverse.getLast (by simpa) := by
    simp only [reverse_reverse]
  rw [this, getLast_reverse]

theorem head!_reverse_of_ne_nil [Inhabited α] (l : List α) (hl : l ≠ []) :
    l.reverse.head ((not_congr List.reverse_eq_nil_iff).mpr hl) = l.getLast hl := by
  have : l.getLast hl = l.reverse.reverse.getLast (by simpa) := by
    simp only [reverse_reverse]
  rw [this, getLast_reverse]

lemma getElem_filter {l : List α} {p : α → Bool} {n : ℕ} (h : n < (l.filter p).length) :
    p (l.filter p)[n] := of_mem_filter ((l.filter p).getElem_mem h)

lemma getElem_inj {l : List α} {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hnodup : l.Nodup) (heq : l[i] = l[j]) :
    i = j := by
  apply List.getElem?_inj hi hnodup
  sorry

lemma sym2_notDiag_length [DecidableEq α] {l : List α} (h : l.Nodup) :
    (l.sym2.filter (¬·.IsDiag)).length = l.length.choose 2 := by
  sorry

lemma singlton_ne_nil {a : α} : [a] ≠ [] := by
  simp only [ne_eq, cons_ne_self, not_false_eq_true]

lemma eq_nil_of_IsEmpty [IsEmpty α] (l : List α) : l = [] := by
  rcases l with _ | ⟨h, t⟩
  rfl
  exact IsEmpty.elim (by assumption) h

/- ------------------------------------------------------------------------------------ -/


lemma subsingleton_of_tail_eq_nil {l : List α} (h : l.tail = []) :
  l = [] ∨ ∃ x, l = [x] := by
  match l with
  | [] => simp only [ne_cons_self, exists_false, or_false]
  | x :: xs =>
    rw [tail_cons] at h
    simp [h]

lemma length_le_one_of_tail_eq_nil {l : List α} (h : l.tail = []) :
  l.length ≤ 1 := by
  rcases subsingleton_of_tail_eq_nil h with rfl | ⟨x, rfl⟩ <;> simp

lemma tail_eq_drop_one (l : List α) :
  l.tail = l.drop 1 := (drop_one l).symm

---------------------------------------------------------------------------
