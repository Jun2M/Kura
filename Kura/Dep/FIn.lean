import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic


namespace Fin

-- theorem succ_val_eq_val_succ {n : ℕ} (i : Fin (n+1)) (hi : i < last _) :
--     (i+1).val = i.val +1 := by


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
