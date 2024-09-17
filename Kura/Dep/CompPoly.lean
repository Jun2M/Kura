import Mathlib.Tactic


/-- Polynomial in Mathlib is not computable.
  This is.
  e.g. [2, 3] = 2x + 3 -/
structure CompPoly (α : Type u) [Ring α] [DecidableEq α] where
  toList : List α
  last_nezero : (h : toList ≠ []) → toList.head h ≠ 0

namespace CompPoly
variable {α : Type u} [Ring α] [DecidableEq α] (p : CompPoly α)

@[simp]
def length : ℕ := p.toList.length

private def rm_zero : List α → List α
  | [] => []
  | a :: l => if a = 0
    then rm_zero l
    else a :: l

private lemma rm_zero.prop (l : List α) : (h : rm_zero l ≠ []) → (rm_zero l).head h ≠ 0 := by
  intro h
  induction l with
  | nil => simp only [rm_zero, ne_eq, not_true_eq_false] at h
  | cons a l ih =>
    simp only [rm_zero]
    by_cases ha : a = 0
    · simp only [rm_zero, ha, ↓reduceIte, ne_eq] at h ⊢
      exact ih h
    · simp only [ha, ↓reduceIte, List.head_cons, ne_eq, not_false_eq_true]

@[simp]
def get (n : ℕ) : α := p.toList.getD n 0

def ofList (l : List α) : CompPoly α where
  toList := rm_zero l
  last_nezero := by
    intro h
    exact rm_zero.prop l h

def toPolynomial (p : CompPoly α) : Polynomial α where
  toFinsupp := {
    toFun := (p.get ·)
    support := (Finset.range p.length).filter (p.get · ≠ 0)
    mem_support_toFun := by
      intro n
      simp only [get, ne_eq, length, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
      intro h0
      contrapose! h0
      exact List.getD_eq_default p.toList 0 h0}

def AddCommGroup : AddCommGroup (CompPoly α) where
add p1 p2 := ofList (p1.toList.zipWithAll (λ a b => a.getD 0 + b.getD 0) p2.toList)
add_comm := sorry
add_assoc := sorry
zero := ofList []
zero_add := sorry
add_zero := sorry
neg p := ofList (p.toList.map (· * -1))
neg_add_cancel := sorry
nsmul := λ n p => ofList (p.toList.map (· * n))
nsmul_zero := sorry
nsmul_succ := sorry
zsmul := λ n p => ofList (p.toList.map (· * n))
zsmul_zero' := sorry
zsmul_succ' := sorry
zsmul_neg' := sorry

def eval (a : α) := p.toList.foldl (λ acc b => acc * a + b) 0

end CompPoly
