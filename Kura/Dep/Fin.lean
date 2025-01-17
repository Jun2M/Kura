import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic


namespace Fin

-- theorem succ_val_eq_val_succ {n : ℕ} (i : Fin (n+1)) (hi : i < last _) :
--     (i+1).val = i.val +1 := by


theorem succ_ne_castSucc {n : ℕ} (i : Fin n) : i.succ ≠ i.castSucc := by
  by_contra! h
  apply_fun Fin.val at h
  simp only [val_succ, coe_castSucc, add_right_eq_self, one_ne_zero] at h

theorem succ_eq_castSucc {n : ℕ} (i j : Fin (n+1)) (h : i.succ = j.castSucc) : i +1 = j := by
  have := h ▸ Fin.castSucc_lt_last j
  rw [← Fin.succ_last, Fin.succ_lt_succ_iff] at this
  sorry

  -- unfold castSucc castAdd succ at h
  -- simp only [castLE] at h
  -- apply_fun Fin.val at h ⊢
  -- simp only at h ⊢
  -- rw [← h]
  -- clear h

@[simp]
lemma castPred_succ {n : ℕ} (i : Fin (n+1)) (hi : i ≠ last n) : (i.castPred hi).succ = i + 1 := by
  ext
  simp only [val_succ, coe_castPred]
  rw [Fin.val_add_one_of_lt]
  exact lt_last_iff_ne_last.mpr hi

@[simp]
lemma castSucc_ne_last {n : ℕ} (i : Fin n) : i.castSucc ≠ last n :=
  ne_last_of_lt <| Fin.castSucc_lt_last i

@[simp]
lemma natAdd_inj {n : ℕ} (i j : Fin n) (m : ℕ) : i.natAdd m = j.natAdd m ↔ i = j := by
  constructor <;> intro h
  · rwa [← Fin.natAddEmb_apply, ← Fin.natAddEmb_apply, (Fin.natAddEmb m).apply_eq_iff_eq] at h
  · rw [h]

lemma natAdd_injective {n : ℕ} (m : ℕ) :
    Function.Injective (Fin.natAdd m : Fin n → Fin (m + n)) := by
  intro i j h
  rwa [natAdd_inj i j m] at h

@[simp]
lemma ext_iff' {n : ℕ} (i j : Fin n) : i = j ↔ i.val = j.val := Fin.ext_iff

@[simp]
lemma le_iff_le {n : ℕ} (i j : Fin n) : i ≤ j ↔ i.val ≤ j.val := by exact le_def

end Fin
