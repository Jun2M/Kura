import Kura.Basic


open Set Function List Nat
variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f g : β}
namespace Graph


structure Walk (G : Graph α β) (u v : α) where
  vx : List α
  edge : List β
  hlen : vx.length = edge.length + 1
  hInc1 : ∀ (i : ℕ) (h : i < edge.length),
    G.Inc (vx[i]'(hlen ▸ Nat.lt_add_right 1 h)) edge[i]
  hInc2 : ∀ (i : ℕ) (h : i < edge.length),
    G.Inc (vx[i + 1]'(hlen ▸ (Nat.add_lt_add_right h 1))) edge[i]
  hstart : vx.head (List.ne_nil_of_length_eq_add_one hlen) = u
  hend : vx.getLast (List.ne_nil_of_length_eq_add_one hlen) = v

namespace Walk

def reverse (w : Walk G u v) : Walk G v u where
  vx := w.vx.reverse
  edge := w.edge.reverse
  hlen := by simp only [length_reverse, w.hlen]
  hInc1 i hi := by
    simp_rw [getElem_reverse, hlen, Nat.add_sub_cancel, Nat.sub_right_comm]
    convert w.hInc2 _ _ using 2
    rw [Nat.sub_add_cancel]
    rw [length_reverse] at hi
    omega
  hInc2 i hi := by
    simp_rw [getElem_reverse, hlen, Nat.add_sub_cancel, sub_add_eq, Nat.sub_right_comm]
    convert w.hInc1 _ _ using 2
  hstart := by
    rw [head_reverse]
    exact w.hend
  hend := by
    rw [getLast_reverse]
    exact w.hstart

def append (w₁ : Walk G u v) (w₂ : Walk G v w) : Walk G u w where
  vx := w₁.vx ++ w₂.vx.tail
  edge := w₁.edge ++ w₂.edge
  hlen := by simp [w₁.hlen, w₂.hlen]; omega
  hInc1 i hi := by
    rw [w₁.edge.getElem_append]
    obtain hilt | rfl | hlti := lt_trichotomy i w₁.edge.length
    · simp_rw [getElem_append, w₁.hlen]
      have : i < w₁.edge.length + 1 := by omega
      simp only [this, ↓reduceDIte, hilt, w₁.hInc1]
    · simp only [getElem_append, w₁.hlen, lt_add_iff_pos_right, lt_one_iff, pos_of_gt, ↓reduceDIte,
      lt_self_iff_false, tsub_self]
      convert w₂.hInc1 0 _ using 1
      · rw [getElem_zero_eq_head, w₂.hstart]
        convert w₁.hend
        rw [← getElem_length_sub_one_eq_getLast]
        simp only [w₁.hlen, add_tsub_cancel_right]
        rw [w₁.hlen]
        omega
      · simpa only [length_append, lt_add_iff_pos_right] using hi
    · have : ¬ i < w₁.edge.length + 1 := by omega
      simp [getElem_append, w₁.hlen, hlti.not_lt, this, sub_add_eq]
      convert w₂.hInc1 _ _ using 2
      · omega
      · simp at hi
        omega
  hInc2 i hi := by
    rw [w₁.edge.getElem_append]
    obtain hilt | rfl | hlti := lt_trichotomy i w₁.edge.length
    · simp_rw [getElem_append, w₁.hlen]
      have : i < w₁.edge.length + 1 := by omega
      simp only [add_lt_add_iff_right, hilt, ↓reduceDIte, w₁.hInc2]
    · simp only [getElem_append, w₁.hlen, lt_self_iff_false, ↓reduceDIte, tsub_self, getElem_tail,
      zero_add]
      convert w₂.hInc2 0 _
    · have : ¬ i < w₁.edge.length + 1 := by omega
      simp [getElem_append, w₁.hlen, hlti.not_lt, this, sub_add_eq]
      convert w₂.hInc2 _ _ using 2
      · omega
      · simp at hi
        omega
  hstart := by
    have : ¬ w₁.vx.isEmpty := by
      rw [isEmpty_iff_length_eq_zero, w₁.hlen]
      omega
    simp only [head_append, this, Bool.false_eq_true, ↓reduceDIte]
    exact w₁.hstart
  hend := by
    simp [getLast_append, w₁.hend, w₂.hend]
    intro h
    rw [← w₂.hstart]
    convert w₂.hend using 1
    have : w₂.vx = [v] := by rw [← head_cons_tail w₂.vx, h, hstart]
    simp only [this, head_cons, getLast_singleton]

