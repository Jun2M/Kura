import Mathlib.Tactic


/-- Polynomial in Mathlib is not computable.
  This is.
  e.g. [2, 3] = 2x + 3 -/
structure CompPoly (α : Type u) [Ring α] [DecidableEq α] where
  toList : List α
  last_nezero : (h : toList ≠ []) → toList.head h ≠ 0

namespace CompPoly
variable {α : Type u} [Ring α] [DecidableEq α] (p : CompPoly α)

instance [Repr α] : Repr (CompPoly α) where
  reprPrec p _ := "CompPoly " ++ repr p.toList

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

instance : Inhabited (CompPoly α) where
  default := ofList [1]

def shifts_aux (n : ℕ) (res : List (CompPoly α)) : List (CompPoly α) :=
  match n with
  | 0 => res
  | n + 1 => shifts_aux n (ofList (res.head!.toList ++ [0]) :: res)

def shifts (n : ℕ) : List (CompPoly α) :=
  shifts_aux n [p]

instance : Add (CompPoly α) where
  add p1 p2 := ofList (p1.toList.reverse.zipWithAll (λ a b => a.getD 0 + b.getD 0) p2.toList.reverse).reverse

instance : Zero (CompPoly α) where
  zero := ofList []

instance : Neg (CompPoly α) where
  neg p := ofList (p.toList.map (· * -1))

instance : CommRing (CompPoly α) where
  add_comm := sorry
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  neg_add_cancel := sorry
  nsmul := λ n p => ofList (p.toList.map (· * n))
  nsmul_zero := sorry
  nsmul_succ := sorry
  zsmul := λ n p => ofList (p.toList.map (· * n))
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  mul p1 p2 :=
    shifts p1 (p2.length -1)
    |>.zipWith (λ p1 a2 => ofList <| p1.toList.map (· * a2)) p2.toList
    |>.sum
  mul_assoc := sorry
  mul_comm := sorry
  one := ofList [1]
  one_mul := sorry
  mul_one := sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry

def eval (a : α) := p.toList.foldl (λ acc b => acc * a + b) 0

def powers_aux (n : ℕ) (res : List (CompPoly α)) : List (CompPoly α) :=
  match n with
  | 0 => res
  | n + 1 => powers_aux n ((res.head! * p) :: res)

def powers (n : ℕ) : List (CompPoly α) :=
  powers_aux p n [ofList [1]]

/-- Composition of polynomials (p ∘ q)(x) = p(q(x)) -/
def comp (q : CompPoly α) : CompPoly α :=
  powers q (p.length - 1)
  |>.zipWith (fun p a ↦ ofList (p.toList.map (· * a))) p.toList
  |>.sum

def truncate (n : ℕ) : CompPoly α :=
  ofList (p.toList.reverse.take n).reverse

def exp (n : ℕ) : CompPoly ℚ :=
  ofList (List.range n |>.map (λ i => (1:ℚ) / i.factorial)).reverse

def div_aux (p q r : CompPoly ℚ) (n : ℕ) : CompPoly ℚ :=
  match n with
  | 0 => r
  | n + 1 =>
    let a := (p - r * q).toList.reverse[r.length]! / q.toList.getLast!
    div_aux p q (ofList (a :: r.toList)) n

def div (p q : CompPoly ℚ) (n : ℕ) : CompPoly ℚ :=
  div_aux p q (ofList []) n

#eval! div 1 (ofList [4, -16, 19, -8, 1]) 10
-- \frac{2x(2-x)}{1-5x+2x^2}
#eval! div (ofList [-2, 4]) (ofList [2, -5, 1]) 10

#eval! (ofList [22605, 4920, (1061:ℚ), 224, 45, 8, 1]) * (ofList [4, -16, 19, -8, 1])
#eval! (ofList [22605, 4920, (1061:ℚ), 224, 45, 8, 1]) * (ofList [-4, 14, -14, 4, 0])
--
#eval! (ofList [374, (82:ℚ), 18, 4, 0]) * (ofList [4, -16, 19, -8, 1])

-- #eval! exp 20
-- #eval! (exp 20).comp (ofList [-1, 0]) * (ofList [1, 0]) |>.powers 5 |>.map (λ p => truncate p 20)
#eval! (exp 20).comp (ofList [-1, 0]) * (ofList [1, 0])
  |>.comp (ofList [54/5, 125/24, 16/6, 3/2, 1, 1, 0])
  |>.truncate 20
#eval! (ofList [(54/5:ℚ), 125/24, 16/6, 3/2, 1, 1, 0])
  |>.comp ((exp 20).comp (ofList [-1, 0]) * (ofList [1, 0]))
  |>.truncate 20


def choose (r : ℚ) (k : ℕ) : ℚ :=
  List.range k |>.foldl (λ acc i => acc * (r - i) / (i+1)) 1

#eval! choose (1/2) 4

def f (n : ℕ) : CompPoly ℚ :=
  ofList (List.range n |>.map (λ (i:ℕ) => 2 / (i+2) * choose (3*i/2) i)).reverse - 1

def g (n : ℕ) : CompPoly ℚ :=
  ofList (List.range n |>.map (λ (i:ℕ) => choose (3*(i-1)/2) ((i-1)/2) / i)).reverse

#eval! g 20


end CompPoly
