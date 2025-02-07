import Mathlib.Data.List.Sym
import Mathlib.Data.List.DropRight
import Batteries.Data.Nat.Basic


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
  rw [takeWhile_append]
  split_ifs with h
  · simp only [ha, Bool.false_eq_true, not_false_eq_true, takeWhile_cons_of_neg, append_nil,
    (l.reverse.takeWhile_prefix p).eq_of_length h]
  · rfl

lemma rdropWhile_append_rtakeWhile (p : α → Bool) (l : List α) :
  (l.rdropWhile p) ++ l.rtakeWhile p = l := by
  induction l with
  | nil => simp only [rdropWhile_nil, rtakeWhile_nil, append_nil]
  | cons a as ih =>
    simp only [rdropWhile, rtakeWhile]
    rw [← reverse_append, List.reverse_eq_iff]
    apply List.takeWhile_append_dropWhile

lemma Chain'.dropLast {r : α → α → Prop} {l : List α} (h : Chain' r l) :
  Chain' r l.dropLast := by
  rw [List.dropLast_eq_take]
  exact take h (l.length - 1)

lemma Chain'.rotate {r : α → α → Prop} {l : List α} (h : Chain' r l) (n : ℕ)
    (h' : ∀ (x : α), x ∈ l.getLast? → ∀ (y : α), y ∈ l.head? → r x y) : Chain' r (l.rotate n) := by
  rw [List.rotate_eq_drop_append_take_mod]
  refine List.Chain'.append (drop h (n % l.length)) (take h (n % l.length)) ?_
  rintro x hx y hy
  refine h' x ?_ y ?_
  · rw [List.getLast?_drop] at hx
    split_ifs at hx with hlen
    · simp only [Option.mem_def, reduceCtorEq] at hx
    · assumption
  · rw [List.head?_take] at hy
    split_ifs at hy with hlen
    · simp only [Option.mem_def, reduceCtorEq] at hy
    · assumption

def skip [DecidableEq α] (l : List α) : List α :=
match l with
| [] => []
| a :: as => a :: skip (as.rtakeWhile (· != a))
termination_by l.length
decreasing_by
  suffices (as.rtakeWhile (· != a)).length ≤ as.length by simp only [length_cons, gt_iff_lt]; omega
  exact rtakeWhile_length_le_length (· != a) as

@[simp]
lemma skip_nil [DecidableEq α] : ([] : List α).skip = [] := by
  unfold skip
  rfl

@[simp]
lemma skip_ne_nil [DecidableEq α] {l : List α} : l.skip ≠ [] ↔ l ≠ [] := by
  rw [not_iff_not]
  match l with
  | [] => simp only [skip_nil]
  | a :: as => simp only [skip, cons_ne_nil]

@[simp]
lemma skip_head? [DecidableEq α] : ∀ {l : List α}, l.skip.head? = l.head?
| [] => by simp only [skip_nil, head?_nil]
| a :: as => by simp only [skip, head?_cons]

@[simp]
lemma skip_getLast? [DecidableEq α] {l : List α} : l.skip.getLast? = l.getLast? := by
  induction l using Nat.strongRecMeasure with
  | f l => exact l.length
  | ind l ih => match l with
  | [] => simp only [skip_nil, length_nil, Nat.zero_le]
  | a :: as =>
      simp only [length_cons, Nat.lt_add_one_iff, skip, getLast?_cons, Option.some.injEq] at ih ⊢
      rw [ih (as.rtakeWhile (· != a)) (as.rtakeWhile_length_le_length _)]; clear ih l
      by_cases h : as.rtakeWhile (· != a) = []
      · by_cases h' : as = [] <;> rw [h] <;> simp_all only [rtakeWhile_eq_nil_iff, ne_eq,
        not_false_eq_true, bne_iff_ne, getLast_eq_iff_getLast?_eq_some, Decidable.not_not,
        forall_const, getLast?_nil, Option.getD_none, Option.getD_some]
      · have := (as.rtakeWhile_suffix _).ne_nil h
        rw [getLast?_eq_getLast_of_ne_nil h, Option.getD_some, getLast?_eq_getLast_of_ne_nil this]
        exact (as.rtakeWhile_suffix _).getLast h

lemma skip_length_le [DecidableEq α] (l : List α) : (l.skip).length ≤ l.length := by
  induction l using Nat.strongRecMeasure with
  | f l => exact l.length
  | ind l ih => match l with
  | [] => simp only [skip_nil, length_nil, Nat.zero_le]
  | a :: as =>
      simp only [length_cons, Nat.lt_add_one_iff, skip, Nat.add_le_add_iff_right, ge_iff_le] at ih ⊢
      have := rtakeWhile_length_le_length (· != a) as
      refine (ih (as.rtakeWhile (· != a)) this).trans this

lemma skip_sublist [DecidableEq α] (l : List α) : l.skip <+ l := by
  induction l using Nat.strongRecMeasure with
  | f l => exact l.length
  | ind l ih => match l with
  | [] => simp only [skip_nil, Sublist.refl]
  | a :: as =>
      simp only [length_cons, Nat.lt_add_one_iff, skip, cons_sublist_cons] at ih ⊢
      refine ih (as.rtakeWhile (· != a)) (as.rtakeWhile_length_le_length _) |>.trans ?_
      rw [List.rtakeWhile, ← List.sublist_reverse_iff]
      exact takeWhile_sublist (· != a)

lemma skip_nodup [DecidableEq α] (l : List α) : (l.skip).Nodup := by
  induction l using Nat.strongRecMeasure with
  | f l => exact l.length
  | ind l ih => match l with
  | [] => simp only [skip_nil, nodup_nil]
  | a :: as =>
      simp only [length_cons, Nat.lt_add_one_iff, skip, nodup_cons] at ih ⊢
      refine ⟨?_, ih (as.rtakeWhile (· != a)) (as.rtakeWhile_length_le_length _)⟩
      apply not_imp_not.mpr (as.rtakeWhile (· != a)).skip_sublist.mem
      apply not_imp_not.mpr List.mem_rtakeWhile_imp
      simp only [bne_self_eq_false, Bool.false_eq_true, not_false_eq_true]

lemma Chain'.skip [DecidableEq α] {r : α → α → Prop} {l : List α} (h : Chain' r l) :
  Chain' r l.skip := by
  induction l using Nat.strongRecMeasure with
  | f l => exact l.length
  | ind l ih =>
    match l with
    | [] => simp only [skip_nil, chain'_nil]
    | [a] => simp only [List.skip, rtakeWhile_nil, skip_nil, chain'_singleton]
    | a :: b :: as =>
      rw [List.chain'_cons', ← (b :: as).rdropWhile_append_rtakeWhile (· != a),
        List.chain'_append] at h
      obtain ⟨hhead, _hdw, htw, hbtw⟩ := h
      simp only [length_cons, Nat.lt_add_one_iff, List.skip, List.chain'_cons', skip_head?] at ih ⊢
      refine ⟨?_, ih ((b :: as).rtakeWhile (· != a)) ((b :: as).rtakeWhile_length_le_length _) htw⟩
      rintro c hc
      by_cases h : (b :: as).rdropWhile (· != a) = []
      · have : (b :: as).rtakeWhile (· != a) = b :: as := by
          conv_rhs => rw [← rdropWhile_append_rtakeWhile (· != a) (b :: as)]
          exact self_eq_append_left.mpr h
        simp only [this, head?_cons, Option.some.injEq, h, nil_append, Option.mem_def,
          forall_eq'] at hc hhead
        exact hc ▸ hhead
      · refine hbtw a ?_ c hc
        have := List.rdropWhile_last_not _ _ h
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
        simpa only [getLast?_eq_getLast_of_ne_nil h, Option.mem_def, Option.some.injEq]

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
    rw [getLast?_eq_getLast_of_ne_nil (skip_ne_nil.mpr <| cons_ne_nil a l),
      getLast?_eq_getLast_of_ne_nil (cons_ne_nil a l), Option.some_inj] at this
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

theorem mem_head?_eq_head : ∀ {l : List α} {x : α}, x ∈ l.head? →
    ∃ (hx : l ≠ []), x = l.head hx
| [], x, hx => by simp only [head?_nil, Option.mem_def, reduceCtorEq] at hx
| a :: as, x, hx => by
  have : a = x := by simpa using hx
  simp only [this, head_cons, ne_eq, reduceCtorEq, not_false_eq_true, exists_const]

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


-- Given an infix `ll` of `l`, split `l` into three parts: the prefix of `ll`, `ll`, and the suffix of `ll`.
def splitByInfix.loop [DecidableEq α] (l ll p : List α) (hl : ll <:+: l) : List α × List α × List α :=
match l with
| [] => (p.reverse, [], [])
| a :: l => if h : ll = (a :: l).take ll.length
  then (p.reverse, ll, (a :: l).drop ll.length)
  else (splitByInfix.loop l ll (a :: p) (by
    rw [← List.prefix_iff_eq_take] at h
    simpa only [infix_cons_iff, h, false_or] using hl))

-- Given an infix `ll` of `l`, split `l` into three parts: the prefix of `ll`, `ll`, and the suffix of `ll`.
def splitByInfix [DecidableEq α] (l ll : List α) (hl : ll <:+: l) : List α × List α × List α :=
  splitByInfix.loop l ll [] hl

lemma splitByInfix.loop_nil [DecidableEq α] {l p : List α} (hl : [] <:+: l) :
    let (p', ll', l') := splitByInfix.loop l [] p hl
    p' = p.reverse ∧ ll' = [] ∧ l' = l := by
  match l with
  | [] => simp only [loop, and_self]
  | a :: l => simp only [loop, length_nil, take_zero, ↓reduceDIte, drop_zero, and_self]

lemma splitByInfix.loop_append [DecidableEq α] {l ll p : List α} (hl : ll <:+: l) :
    let (p', ll', l') := splitByInfix.loop l ll p hl
    p' ++ ll' ++ l' = p.reverse ++ l := by
  induction l generalizing p with
  | nil =>
    rw [infix_nil] at hl
    subst ll
    simp only [loop, append_nil]
  | cons a l ih =>
    by_cases h : ll = (a :: l).take ll.length
    · simp [splitByInfix.loop, ← h, eq_self_iff_true, if_true]
      conv_rhs => rw [← (a :: l).take_append_drop ll.length]
      rw [← h, append_right_inj]
    · simp only [loop, h, ↓reduceDIte, append_assoc]
      simp only [append_assoc] at ih
      rw [← List.prefix_iff_eq_take] at h
      simp only [infix_cons_iff, h, false_or] at hl
      rw [ih (p := a :: p) hl]
      simp only [reverse_cons, append_assoc, singleton_append]

lemma splitByInfix_nil [DecidableEq α] {l : List α} (hl : [] <:+: l) :
    let (A, ll, B) := splitByInfix l [] hl
    A = [] ∧ ll = [] ∧ B = l := by
  unfold splitByInfix
  exact splitByInfix.loop_nil hl

lemma splitByInfix_append [DecidableEq α] {l ll : List α} (hl : ll <:+: l) :
    let (A, ll, B) := splitByInfix l ll hl
    A ++ ll ++ B = l := by
  unfold splitByInfix
  exact splitByInfix.loop_append hl

lemma IsPrefix.Nodup [DecidableEq α] {l p : List α} (h : p <+: l) (hnodup : l.Nodup) : p.Nodup := by
  obtain ⟨_o, rfl⟩ := h
  exact Nodup.of_append_left hnodup

lemma IsSuffix.Nodup [DecidableEq α] {l p : List α} (h : p <:+ l) (hnodup : l.Nodup) : p.Nodup := by
  obtain ⟨_o, rfl⟩ := h
  exact Nodup.of_append_right hnodup

lemma IsInfix.Nodup [DecidableEq α] {l p : List α} (h : p <:+: l) (hnodup : l.Nodup) : p.Nodup := by
  obtain ⟨o, l, rfl⟩ := h
  exact Nodup.of_append_right <| Nodup.of_append_left hnodup

-- lemma head?_dropWhile_eq_find? {l : List α} {p : α → Bool} :
--     (List.dropWhile (¬ p ·) l).head? = List.find? p l := by
--   induction l with
--   | nil => simp only [dropWhile_nil, head?_nil, find?_nil]
--   | cons a l ih =>
--     by_cases h : p a
--     · rw [find?_cons_of_pos _ h, dropWhile_cons_of_neg (by simp_all), head?_cons]
--     · rwa [find?_cons_of_neg _ h, dropWhile_cons_of_pos (by simp_all)]

lemma eq_dropWhile_head_of_mem_find? {l : List α} {p : α → Bool} {a : α} (h : a ∈ List.find? p l)
    (h' : List.dropWhile (!p ·) l ≠ []) : a = (List.dropWhile (!p ·) l).head h' := by
  rw [find?_eq_head?_dropWhile_not] at h
  rwa [eq_comm, head_eq_iff_head?_eq_some h']

lemma takeWhile_ne_find?_eq_takeWhile [DecidableEq α] {l : List α} {p : α → Bool} {a : α}
    (h : a ∈ List.find? p l) : List.takeWhile (· ≠ a) l = List.takeWhile (! p ·) l := by
  induction l with
  | nil => simp only [find?_nil, Option.mem_def, reduceCtorEq] at h
  | cons b l ih =>
    by_cases h' : p b
    · rw [takeWhile_cons_of_neg, takeWhile_cons_of_neg]
      exact Bool.not_not_eq.mpr h'
      simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
        Decidable.not_not]
      simpa only [find?_cons_of_pos _ h', Option.mem_def, Option.some.injEq] using h
    · rw [find?_cons_of_neg _ h'] at h
      rw [takeWhile_cons_of_pos, takeWhile_cons_of_pos, cons_inj_right, ih h]
      exact Bool.not_iff_not.mpr h'
      simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      rintro rfl
      exact h' <| List.find?_some h

lemma dropWhile_ne_find?_eq_dropWhile [DecidableEq α] {l : List α} {p : α → Bool} {a : α}
    (h : a ∈ List.find? p l) : List.dropWhile (· ≠ a) l = List.dropWhile (! p ·) l := by
  induction l with
  | nil => simp only [find?_nil, Option.mem_def, reduceCtorEq] at h
  | cons b l ih =>
    by_cases h' : p b
    · rw [dropWhile_cons_of_neg, dropWhile_cons_of_neg]
      exact Bool.not_not_eq.mpr h'
      simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
        Decidable.not_not]
      simpa only [find?_cons_of_pos _ h', Option.mem_def, Option.some.injEq] using h
    · rw [find?_cons_of_neg _ h'] at h
      rw [dropWhile_cons_of_pos, dropWhile_cons_of_pos, ih h]
      exact Bool.not_iff_not.mpr h'
      simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
        Decidable.not_not]
      rintro rfl
      exact h' <| List.find?_some h

lemma singlton_ne_nil {a : α} : [a] ≠ [] := by
  simp only [ne_eq, cons_ne_self, not_false_eq_true]

lemma eq_nil_of_IsEmpty [IsEmpty α] (l : List α) : l = [] := by
  rcases l with _ | ⟨h, t⟩
  rfl
  exact IsEmpty.elim (by assumption) h

lemma forall₂_iff_forall {l : List α} {P : α → α → Prop} :
    List.Forall₂ P l l ↔ List.Forall (fun a ↦ P a a) l := by
  rw [List.forall₂_same, List.forall_iff_forall_mem]

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
