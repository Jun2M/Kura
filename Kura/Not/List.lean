import Mathlib.Data.List.Basic


namespace List
variable {α : Type _}

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

theorem head_append_of_ne_nil (hl : l₁ ≠ []) :
    (l₁ ++ l₂).head (by simp [hl]) = l₁.head hl := by
  match l₁ with
  | nil => contradiction
  | cons x xs => rfl

theorem head_reverse_of_ne_nil (l : List α) (hl : l ≠ []) :
    l.reverse.head ((not_congr List.reverse_eq_nil_iff).mpr hl) = l.getLast hl := by
  have : l.getLast hl = l.reverse.reverse.getLast (by simpa) := by
    simp only [reverse_reverse]
  rw [this, getLast_reverse]
  exact (get_zero_eq_head_of_ne_nil _).symm

theorem head!_reverse_of_ne_nil [Inhabited α] (l : List α) (hl : l ≠ []) :
    l.reverse.head ((not_congr List.reverse_eq_nil_iff).mpr hl) = l.getLast hl := by
  have : l.getLast hl = l.reverse.reverse.getLast (by simpa) := by
    simp only [reverse_reverse]
  rw [this, getLast_reverse]
  exact (get_zero_eq_head_of_ne_nil _).symm

/- ------------------------------------------------------------------------------------ -/


lemma subsingleton_of_tail_eq_nil {l : List α} (h : l.tail = []) :
  l = [] ∨ ∃ x, l = [x] := by
  match l with
  | [] => simp only [exists_false, or_false]
  | x :: xs =>
    rw [tail_cons] at h
    simp [h]

lemma length_le_one_of_tail_eq_nil {l : List α} (h : l.tail = []) :
  l.length ≤ 1 := by
  rcases subsingleton_of_tail_eq_nil h with rfl | ⟨x, rfl⟩ <;> simp

lemma tail_eq_drop_one (l : List α) :
  l.tail = l.drop 1 := (drop_one l).symm

---------------------------------------------------------------------------
