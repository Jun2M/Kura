import Mathlib

theorem exist_le_sum_div_card {ι F : Type*} [LinearOrderedField F] {f : ι → F} {s : Finset ι} (hs : s.Nonempty)
  : ∃ i, f i ≤ (∑ i ∈ s, f i) / s.card := by
  by_contra! h
  apply lt_irrefl (∑ i in s, f i)
  conv_lhs => rw [← div_mul_cancel₀ (∑ i ∈ s, f i) (by simp; exact Finset.nonempty_iff_ne_empty.mp hs : (s.card : F) ≠ 0)]
  rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_lt_sum_of_nonempty hs (fun i _ => h i)

theorem nexist_le_sum_div_card {ι F : Type*}
    [Fintype ι] [Nonempty ι] [LinearOrderedField F] {f : ι → F} :
    ∃ i, f i ≤ (∑ i, f i) / Fintype.card ι:= by
  classical
  have h := Fintype.exists_sum_fiber_le_of_sum_le_nsmul
              (w := f) (f := id) (b := (∑ i, f i) / Fintype.card ι)
  have : (Fintype.card ι : F) ≠ 0 := by norm_cast; exact NeZero.ne (Fintype.card ι)
  simp only [nsmul_eq_mul, mul_div_cancel₀ _ this, le_refl, true_imp_iff] at h
  convert h using 3 with i
  simp [Finset.filter_eq' Finset.univ i]
