import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic
import Kura.Dep.Toss
import Mathlib.Data.Nat.ChineseRemainder


@[simp]
lemma Nat.pos_of_neZero_simp (n : ℕ) [NeZero n] : n > 0 := Nat.pos_of_neZero n

@[simp]
lemma Nat.sub_one_add_one_eq_self (n : ℕ) [NeZero n] : n - 1 + 1 = n := by
  have := NeZero.one_le (n := n)
  omega

lemma Nat.exist_of_NeZero (n : ℕ) [NeZero n] : ∃ m : ℕ, n = m + 1 := by
  use n - 1
  exact (sub_one_add_one_eq_self n).symm

@[simp]
lemma Nat.ne_zero_of_mod_ne_zero {n m : ℕ} (h : n % m ≠ 0) : n ≠ 0 := by
  by_contra! hn
  subst n
  simp only [zero_mod, ne_eq, not_true_eq_false] at h

lemma Nat.mod_sub_eq_sub_mod {l n m : ℕ} (h : m ≤ l % n): l % n - m = (l - m) % n := by
  induction l, n using Nat.mod.inductionOn with
  | base x y ih =>
    simp at ih
    by_cases hy : y = 0
    · subst y
      simp only [mod_zero]
    · specialize ih (by omega)
      rw [Nat.mod_eq_of_lt ih, eq_comm]
      exact Nat.mod_eq_of_lt (by omega)
  | ind x y ih hh =>
    obtain ⟨h0y, hyx⟩ := ih
    rw [← Nat.mod_eq_sub_mod hyx, Nat.sub_right_comm, ← Nat.mod_eq_sub_mod] at hh
    exact hh h
    clear hh
    have := Nat.div_mul_self_eq_mod_sub_self (x := x) (k := y)
    rw [← add_toss_eq' (by simp only [Nat.div_pos_iff, h0y, hyx, and_self,
      mul_pos_iff_of_pos_left])] at this
    rw [← this, Nat.add_sub_assoc h, ge_iff_le]; clear this
    refine le_add_right_of_le ?_
    nth_rw 1 [← one_mul y, ← Nat.div_self h0y]
    refine Nat.mul_le_mul_right y ?_
    exact Nat.div_le_div_right hyx

@[simp]
lemma Nat.succ_pred' (n : ℕ) [NeZero n] : n.pred.succ = n := Nat.succ_pred (NeZero.ne n)

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

-- @[simp]
lemma le_iff_le {n : ℕ} (i j : Fin n) : i ≤ j ↔ i.val ≤ j.val := le_def

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

def castOfEqRingHom {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    RingHom (Fin n) (Fin m) where
  toFun := Fin.cast h
  map_one' := by
    subst n
    rfl
  map_mul' := by
    subst n
    simp only [cast_eq_self, implies_true]
  map_zero' := by
    subst n
    rfl
  map_add' := by
    subst n
    simp only [cast_eq_self, implies_true]

@[simp]
lemma castOfEqRingHom_apply {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) (i : Fin n) :
    castOfEqRingHom h i = i.cast h := rfl

@[simp]
lemma val_cast {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) (i : Fin n) :
    (i.cast h).val = i.val := by
  subst m
  simp only [cast_eq_self]


lemma val_add_one_of_lt' {n : ℕ} [NeZero n] {i j : Fin n} (h : i.val < j.val) :
    (i + 1).val = i.val + 1 := by
  obtain (_ | m) := n
  · exfalso
    exact i.elim0
  · apply val_add_one_of_lt
    rw [Fin.lt_last_iff_ne_last]
    exact ne_last_of_lt h

def last' (n : ℕ) [NeZero n] : Fin n where
  val := n-1
  isLt := by simp only [tsub_lt_self_iff, Nat.pos_of_neZero_simp, Nat.lt_one_iff, pos_of_gt, and_self]

@[simp]
lemma val_last' {n : ℕ} [NeZero n] : (last' n).val = n-1 := rfl

lemma last_eq_last' {n : ℕ} : last n = last' (n+1) := rfl

lemma last'_eq_last {n : ℕ} [NeZero n] : last' n = (last (n-1)).cast (Nat.sub_one_add_one_eq_self _) := by
  ext
  simp only [val_last', coe_cast, val_last]

@[simp]
lemma neg_one_eq_last' {n : ℕ} [NeZero n] : (-1 : Fin n) = last' n := by
  cases n
  · exfalso; exact (neZero_zero_iff_false (α := ℕ)).mp (by assumption)
  · simp only [neg_one_eq_last, ext_iff', val_last, val_last', add_tsub_cancel_right]

-- @[simp]
lemma eq_last_of_add_one_val_eq_zero {n : ℕ} [NeZero n] {i : Fin n} (h : i + 1 = 0) :
    i = last' n := by
  rw [add_toss_eq, zero_sub] at h
  subst i
  exact neg_one_eq_last'

instance instFinZeroLEOneClass {n : ℕ} [NeZero n] : ZeroLEOneClass (Fin n) where
  zero_le_one := Fin.zero_le' 1

lemma le_last' {n : Nat} [NeZero n] (i : Fin n) : i ≤ last' n := by
  apply Nat.le_of_lt_succ
  simp only [val_last', Nat.succ_eq_add_one, Nat.sub_one_add_one_eq_self, is_lt]

@[simp]
theorem last_le_iff' {n : Nat} [NeZero n] {k : Fin n} : last' n ≤ k ↔ k = last' n := by
  rw [Fin.ext_iff, Nat.le_antisymm_iff, le_def, and_iff_right (by apply le_last')]

@[simp]
theorem le_last_iff' {n : Nat} [NeZero n] {k : Fin n} : k < last' n ↔ k ≠ last' n := by
  rw [ne_eq, ← last_le_iff', not_le]

@[simp]
theorem add_one_le_iff' {n : Nat} [NeZero n] {k : Fin n} : k + 1 ≤ k ↔ k = last' n := by
  obtain ⟨m, hm⟩ := Nat.exist_of_NeZero n
  subst n
  exact add_one_le_iff

lemma lt_add_one_iff' {n : ℕ} {k : Fin n} [NeZero n] : k < k + 1 ↔ k < last' n := by
  rw [← Decidable.not_iff_not, not_lt, not_lt]
  simp

lemma val_add_one' {n : ℕ} {k : Fin n} [NeZero n] : (k + 1).val = if k = last' n then 0 else k.val + 1 := by
  obtain ⟨m, hm⟩ := Nat.exist_of_NeZero n
  subst n
  exact val_add_one k

@[simp]
lemma last'_add_one_eq_zero {n : ℕ} [NeZero n] : last' n + 1 = 0 := by
  obtain ⟨m, hm⟩ := Nat.exist_of_NeZero n
  subst n
  exact last_add_one _

def singleton_comple_equiv_pred' {m : ℕ} [NeZero m]:
    ({-1}ᶜ : Set (Fin m)).Elem ≃ Fin (m - 1) where
  toFun x := x.val.castPred (by
    simp only [ne_eq, ext_iff', val_natCast, Nat.sub_one_add_one_eq_self,
      Nat.mod_eq_of_lt x.val.prop, val_last]
    have := x.prop
    simpa [-Subtype.coe_prop, neg_one_eq_last'] using this)
  invFun x := ⟨x.castSucc, by
    simp only [coe_castSucc, Set.mem_compl_iff, Set.mem_singleton_iff, ext_iff', val_natCast]
    rw [Nat.mod_eq_of_lt (by omega), neg_one_eq_last', val_last']
    exact x.prop.ne⟩
  left_inv x := by simp only [castSucc_castPred, val_natCast, Nat.sub_one_add_one_eq_self,
    Nat.mod_eq_of_lt x.val.prop, cast_val_eq_self, Subtype.coe_eta]
  right_inv x := by
    simp only [coe_castSucc, val_natCast, ext_iff', coe_castPred, Nat.sub_one_add_one_eq_self,
      dvd_refl, Nat.mod_mod_of_dvd]
    exact Nat.mod_eq_of_lt (by omega)

-- lemma OfNat_eq_cast {l n m : ℕ} [NeZero l] [NeZero n] (i : Fin n) :
--     (@OfNat.ofNat (Fin l) m).val.cast = @OfNat.ofNat (Fin n) m := by
--   ext
--   simp [cast_eq_self, cast_val_eq_self]


-- @[simp] lemma coe_sub' {n : Nat} (a b : Fin n) : ↑(a - b) = (n - ↑b + ↑a) % n := Fin.coe_sub a b

end Fin
