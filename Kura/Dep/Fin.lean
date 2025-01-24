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

@[simp]
lemma coe_neg_one' {n : ℕ+} : (-1 : Fin n).val = n - 1 := by
  convert coe_neg_one
  rw [Nat.sub_add_cancel]
  exact n.prop

@[simp]
lemma cast_add {n m : ℕ} (h : n = m) (i j : Fin n) : (i + j).cast h = i.cast h + j.cast h := by
  subst m
  rfl

lemma cast_eq_val_cast {n m : ℕ} [NeZero m] (h : n = m) (i : Fin n) :
    i.cast h = i.val.cast := by
  subst m
  simp only [cast_eq_self, cast_val_eq_self]

@[simp]
lemma neg_one_eq_last {n : ℕ} : (-1 : Fin (n+1)) = last n := by
  ext
  simp only [coe_neg_one, val_last]

@[simp]
lemma neg'_one_eq_last {n : ℕ} : @Neg.neg (Fin (n+1)) SubNegMonoid.toNeg 1 = last n := by
  ext
  simp only [coe_neg_one, val_last]

def singleton_comple_equiv_pred {n : ℕ} {m : ℕ+} (h : m = n + 1) :
    ({-1}ᶜ : Set (Fin m)).Elem ≃ Fin n where
  toFun x := (x.val.cast h).castPred (by
    simp only [coe_cast, val_natCast, h, Nat.mod_eq_of_lt x.val.prop, ne_eq, ext_iff', val_last]
    have := x.prop
    simpa only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff, ext_iff', coe_neg_one', h,
      add_tsub_cancel_right] using this)
  invFun x := ⟨x.castSucc, by
    simp only [coe_castSucc, Set.mem_compl_iff, Set.mem_singleton_iff, ext_iff', val_natCast, h,
      Nat.mod_eq_of_lt (x.prop.trans (lt_add_one n)), coe_neg_one', add_tsub_cancel_right]
    exact Nat.ne_of_lt x.prop⟩
  left_inv x := by simp only [coe_cast, val_natCast, h, Nat.mod_eq_of_lt x.val.prop,
    castSucc_castPred, cast_val_eq_self, Subtype.coe_eta]
  right_inv x := by simp only [coe_castSucc, val_natCast, h, coe_cast, dvd_refl,
    Nat.mod_mod_of_dvd, ext_iff', coe_castPred, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
    x.prop.trans (lt_add_one n)]

lemma cast_surjective {n m : ℕ} (h : n = m) : Function.Surjective (Fin.cast h) := by
  intro i
  subst m
  exact ⟨i.cast rfl, cast_eq_self _⟩

@[simp]
lemma cast_neg {n m : ℕ} [NeZero n] [NeZero m] {h : n = m} {i : Fin n} :
    (-i : Fin n).cast h = (-(i.cast h) : Fin m) := by
  subst m
  simp only [cast_eq_self]

@[simp]
lemma cast_OfNat {n m i: ℕ} [NeZero n] [NeZero m] {h : n = m} :
    ((@OfNat.ofNat (Fin n) i Fin.instOfNat).cast h : Fin m) =
    @OfNat.ofNat (Fin m) i Fin.instOfNat := by
  subst m
  simp only [cast_eq_self]

-- lemma OfNat_eq_cast {l n m : ℕ} [NeZero l] [NeZero n] (i : Fin n) :
--     (@OfNat.ofNat (Fin l) m).val.cast = @OfNat.ofNat (Fin n) m := by
--   ext
--   simp [cast_eq_self, cast_val_eq_self]


-- @[simp] lemma coe_sub' {n : Nat} (a b : Fin n) : ↑(a - b) = (n - ↑b + ↑a) % n := Fin.coe_sub a b

end Fin
