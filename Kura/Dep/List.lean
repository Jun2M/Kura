import Mathlib.Data.List.Sym


namespace List
variable {α : Type _}

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
