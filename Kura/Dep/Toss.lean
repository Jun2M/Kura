import Mathlib.Algebra.Order.Nonneg.Field


-------------------------------------Toss---------------------------------------

theorem toss_add_eq {α : Type} [AddGroup α] {a b c : α} : a + b = c ↔ b = -a + c := by
  rw [
    ← eq_neg_add_iff_add_eq
  ]

theorem Nat.toss_add_eq {a b c : ℕ} (hc : a ≤ c) : a + b = c ↔ b = c - a := by omega

theorem Nat.toss_add_eq' {a b c : ℕ} (hc : 0 < b) : a + b = c ↔ b = c - a := by omega

theorem add_toss_eq {α : Type} [AddGroup α] {a b c : α} : a + b = c ↔ a = c - b := by
  rw [
    ← eq_sub_iff_add_eq
  ]

theorem Nat.add_toss_eq {a b c : ℕ} (hc : b ≤ c) : a + b = c ↔ a = c - b := by omega

theorem Nat.add_toss_eq' {a b c : ℕ} (hc : 0 < a) : a + b = c ↔ a = c - b := by omega

theorem eq_toss_add {α : Type} [AddGroup α] {a b c : α} : a = b + c ↔ -b + a = c := by
  rw [
    ← neg_add_eq_iff_eq_add
  ]

theorem eq_add_toss {α : Type} [AddGroup α] {a b c : α} : a = b + c ↔ a - c = b := by
  rw [
    ← sub_eq_iff_eq_add
  ]

theorem add_eq_toss {α : Type} [AddGroup α] {a b : α} : a = b ↔ a - b = 0 := by
  rw [
    ← sub_eq_zero
  ]

theorem toss_eq_add {α : Type} [AddGroup α] {a b : α} : a = b ↔ 0 = -a + b := by
  rw [← neg_add_eq_zero, eq_comm]

theorem toss_add_le {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a + b ≤ c ↔ b ≤ -a + c := by
  rw [
    ← le_neg_add_iff_add_le
  ]

theorem add_toss_le {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a + b ≤ c ↔ a ≤ c - b := by
  rw [
    ← le_sub_iff_add_le
  ]

theorem le_toss_add {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a ≤ b + c ↔ -b + a ≤ c := by
  rw [
    ← neg_add_le_iff_le_add
  ]

theorem le_add_toss {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a ≤ b + c ↔ a - c ≤ b := by
  rw [
    ← sub_le_iff_le_add
  ]

theorem toss_add_lt {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a + b < c ↔ b < -a + c := by
  rw [
    ← lt_neg_add_iff_add_lt
  ]

theorem add_toss_lt {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a + b < c ↔ a < c - b := by
  rw [
    ← lt_sub_iff_add_lt
  ]

theorem lt_toss_add {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a < b + c ↔ -b + a < c := by
  rw [
    ← neg_add_lt_iff_lt_add
  ]

theorem lt_add_toss {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a < b + c ↔ a - c < b := by
  rw [
    ← sub_lt_iff_lt_add
  ]






theorem toss_sub_eq {α : Type} [AddGroup α] {a b c : α} : a - b = c ↔ -b = -a + c := by
  rw [
    sub_eq_add_neg, toss_add_eq
  ]

theorem sub_toss_eq {α : Type} [AddGroup α] {a b c : α} : a - b = c ↔ a = c + b := by
  exact sub_eq_iff_eq_add

theorem Nat.sub_toss_eq' {a b c : ℕ} (hc : c > 0) : a - b = c ↔ a = c + b := by omega

theorem toss_mul_eq {α : Type} [Group α] {a b c : α} : a * b = c ↔ b = a⁻¹ * c := by
  rw [
    ← eq_inv_mul_iff_mul_eq
  ]

theorem toss_mul_eq₀ {α : Type} [GroupWithZero α] {a b c : α} (han0 : a ≠ 0) : a * b = c ↔ b = a⁻¹ * c := by
  rwa [
    ← eq_inv_mul_iff_mul_eq₀
  ]

theorem mul_toss_eq {α : Type} [Group α] {a b c : α} : a * b = c ↔ a = c * b⁻¹ := by
  rw [
    ← eq_mul_inv_iff_mul_eq
  ]

theorem mul_toss_eq₀ {α : Type} [GroupWithZero α] {a b c : α} (hbn0 : b ≠ 0) : a * b = c ↔ a = c * b⁻¹ := by
  rwa [
    ← eq_mul_inv_iff_mul_eq₀
  ]

theorem eq_toss_mul {α : Type} [Group α] {a b c : α} : a = b * c ↔ b⁻¹ * a = c := by
  rw [
    ← inv_mul_eq_iff_eq_mul
  ]

theorem eq_toss_mul₀ {α : Type} [GroupWithZero α] {a b c : α} (hbn0 : b ≠ 0) : a = b * c ↔ b⁻¹ * a = c := by
  rwa [
    ← inv_mul_eq_iff_eq_mul₀
  ]

theorem eq_mul_toss {α : Type} [Group α] {a b c : α} : a = b * c ↔ a * c⁻¹ = b := by
  rw [
    ← mul_inv_eq_iff_eq_mul
  ]

theorem eq_mul_toss₀ {α : Type} [GroupWithZero α] {a b c : α} (hcn0 : c ≠ 0) : a = b * c ↔ a * c⁻¹ = b := by
  rwa [
    ← mul_inv_eq_iff_eq_mul₀
  ]

theorem mul_eq_toss {α : Type} [Group α] {a b : α} : a = b ↔ a * b⁻¹ = 1 := by
  rw [
    ← mul_inv_eq_one
  ]

theorem mul_eq_toss₀ {α : Type} [GroupWithZero α] {a b : α} (hbn0 : b ≠ 0) : a = b ↔ a * b⁻¹ = 1 := by
  rwa [
    ← mul_inv_eq_one₀
  ]

theorem toss_eq_mul {α : Type} [Group α] {a b : α} : a = b ↔ 1 = a⁻¹ * b := by
  conv_lhs => rw [← inv_mul_eq_one, eq_comm]

theorem toss_div_eq {α : Type} [Group α] {a b c : α} : a / b = c ↔ 1 / b = a⁻¹ * c := by
  rw [Iff.comm, eq_comm, toss_mul_eq, inv_inv, one_div, ← div_eq_mul_inv, eq_comm]

theorem toss_div_eq₀ {α : Type} [GroupWithZero α] {a b c : α} (han0 : a ≠ 0) : a / b = c ↔ 1 / b = a⁻¹ * c := by
  have : a⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero]
    exact han0
  rw [Iff.comm, eq_comm, toss_mul_eq₀ this, inv_inv, one_div, ← div_eq_mul_inv, eq_comm]

theorem div_toss_eq {α : Type} [Group α] {a b c : α} : a / b = c ↔ a = c * b := by
  exact div_eq_iff_eq_mul

theorem div_toss_eq₀ {α : Type} [GroupWithZero α] {a b c : α} (hbn0 : b ≠ 0) : a / b = c ↔ a = c * b := by
  exact div_eq_iff hbn0




theorem toss_sub_le {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a - b ≤ c ↔ -b ≤ -a + c := by
  rw [sub_eq_add_neg]
  exact toss_add_le

theorem sub_toss_le {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a - b ≤ c ↔ a ≤ c + b := by
  exact sub_le_iff_le_add

theorem le_toss_sub {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a ≤ b - c ↔ -b + a ≤ - c := by
  rw [sub_eq_add_neg]
  exact le_toss_add

theorem le_sub_toss {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a ≤ b - c ↔ a + c ≤ b := by
  exact le_sub_iff_add_le

theorem toss_mul_le {α : Type} [OrderedCommGroup α] {a b c : α} :
  a * b ≤ c ↔ b ≤ a⁻¹ * c := by
  rw [
    ← le_inv_mul_iff_mul_le
  ]

theorem toss_mul_le₀ {α : Type} [LinearOrderedCommGroupWithZero α] {a b c : α} (haNe0 : 0 < a) :
  a * b ≤ c ↔ b ≤ a⁻¹ * c := by
  rw [mul_comm _ c, le_mul_inv_iff₀ haNe0, mul_comm]

theorem mul_toss_le {α : Type} [OrderedCommGroup α] {a b c : α} :
  a * b ≤ c ↔ a ≤ c * b⁻¹ := by
  rw [
    ← le_mul_inv_iff_mul_le
  ]

theorem mul_toss_le₀ {α : Type} [LinearOrderedCommGroupWithZero α] {a b c : α} (hbNe0 : 0 < b) :
  a * b ≤ c ↔ a ≤ c * b⁻¹ := by
  rw [le_mul_inv_iff₀ hbNe0, mul_comm]

theorem le_toss_mul {α : Type} [OrderedCommGroup α] {a b c : α} :
  a ≤ b * c ↔ b⁻¹ * a ≤ c := by
  rw [
    ← inv_mul_le_iff_le_mul
  ]

theorem le_toss_mul₀ {α : Type} [LinearOrderedCommGroupWithZero α] {a b c : α} (hbNe0 : 0 < b) :
  a ≤ b * c ↔ b⁻¹ * a ≤ c := by
  rw [mul_comm _ a, mul_inv_le_iff₀ hbNe0, mul_comm]

theorem le_mul_toss {α : Type} [OrderedCommGroup α] {a b c : α} :
  a ≤ b * c ↔ a * c⁻¹ ≤ b := by
  rw [
    ← mul_inv_le_iff_le_mul
  ]

theorem le_mul_toss₀ {α : Type} [LinearOrderedCommGroupWithZero α] {a b c : α} (hcNe0 : 0 < c) :
  a ≤ b * c ↔ a * c⁻¹ ≤ b := by
  rw [mul_inv_le_iff₀ hcNe0, mul_comm]

theorem toss_div_le {α : Type} [OrderedCommGroup α] {a b c : α} :
  a / b ≤ c ↔ 1 / b ≤ a⁻¹ * c := by
  rw [le_inv_mul_iff_mul_le, one_div, ← div_eq_mul_inv]

theorem toss_div_le₀ {α : Type} [LinearOrderedCommGroupWithZero α] {a b c : α} (haNe0 : 0 < a) :
  a / b ≤ c ↔ 1 / b ≤ a⁻¹ * c := by
  rw [div_eq_mul_inv, one_div, toss_mul_le₀ haNe0]

theorem div_toss_le {α : Type} [OrderedCommGroup α] {a b c : α} :
  a / b ≤ c ↔ a ≤ c * b := by
  exact div_le_iff_le_mul

theorem div_toss_le₀ {α : Type} [LinearOrderedCommGroupWithZero α] {a b c : α} (hbNe0 : 0 < b) :
  a / b ≤ c ↔ a ≤ c * b := by
  exact div_le_iff₀ hbNe0

theorem le_toss_div {α : Type} [OrderedCommGroup α] {a b c : α} :
  a ≤ b / c ↔ b⁻¹ * a ≤ c⁻¹ := by
  rw [div_eq_mul_inv]
  exact le_toss_mul

theorem le_toss_div₀ {α : Type} [LinearOrderedCommGroupWithZero α] {a b c : α} (hbNe0 : 0 < b) :
  a ≤ b / c ↔ b⁻¹ * a ≤ c⁻¹ := by
  rw [div_eq_mul_inv]
  exact le_toss_mul₀ hbNe0

theorem le_div_toss {α : Type} [OrderedCommGroup α] {a b c : α} :
  a ≤ b / c ↔ a * c ≤ b := by
  exact le_div_iff_mul_le

theorem le_div_toss₀ {α : Type} [LinearOrderedCommGroupWithZero α] {a b c : α} (hcNe0 : 0 < c) :
  a ≤ b / c ↔ a * c ≤ b := by
  exact le_div_iff₀ hcNe0







theorem toss_sub_lt {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a - b < c ↔ -b < -a + c := by
  rw [sub_eq_add_neg]
  exact toss_add_lt

theorem sub_toss_lt {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a - b < c ↔ a < c + b := by
  exact sub_lt_iff_lt_add

theorem lt_toss_sub {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a < b - c ↔ -b + a < - c := by
  rw [sub_eq_add_neg]
  exact lt_toss_add

theorem lt_sub_toss {α : Type} [OrderedAddCommGroup α] {a b c : α} :
  a < b - c ↔ a + c < b := by
  exact lt_sub_iff_add_lt

theorem toss_mul_lt {α : Type} [OrderedCommGroup α] {a b c : α} :
  a * b < c ↔ b < a⁻¹ * c := by
  rw [
    ← lt_inv_mul_iff_mul_lt
  ]

theorem mul_toss_lt {α : Type} [OrderedCommGroup α] {a b c : α} :
  a * b < c ↔ a < c * b⁻¹ := by
  rw [
    ← lt_mul_inv_iff_mul_lt
  ]

theorem lt_toss_mul {α : Type} [OrderedCommGroup α] {a b c : α} :
  a < b * c ↔ b⁻¹ * a < c := by
  rw [
    ← inv_mul_lt_iff_lt_mul
  ]

theorem lt_mul_toss {α : Type} [OrderedCommGroup α] {a b c : α} :
  a < b * c ↔ a * c⁻¹ < b := by
  rw [
    ← mul_inv_lt_iff_lt_mul
  ]

theorem toss_div_lt {α : Type} [OrderedCommGroup α] {a b c : α} :
  a / b < c ↔ 1 / b < a⁻¹ * c := by
  rw [Iff.comm, lt_inv_mul_iff_mul_lt, one_div, ← div_eq_mul_inv]

theorem div_toss_lt {α : Type} [OrderedCommGroup α] {a b c : α} :
  a / b < c ↔ a < c * b := by
  exact div_lt_iff_lt_mul

theorem lt_toss_div {α : Type} [OrderedCommGroup α] {a b c : α} :
  a < b / c ↔ b⁻¹ * a < c⁻¹ := by
  rw [div_eq_mul_inv]
  exact lt_toss_mul

theorem lt_div_toss {α : Type} [OrderedCommGroup α] {a b c : α} :
  a < b / c ↔ a * c < b := by
  exact lt_div_iff_mul_lt
