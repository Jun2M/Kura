import Mathlib

open List

#eval (finRange 4).permutations

def comp [NeZero n] : List (Fin n) → List (Fin n) → List (Fin n) :=
  fun l1 l2 ↦ l1.map (fun i ↦ l2.get! i)

def inv [NeZero n] : List (Fin n) → List (Fin n) :=
  fun l ↦ ([0, 1, 2, 3] : List (Fin 4)).map (fun i ↦ l.findIdx (fun j ↦ j = i))

#eval comp ([2, 3, 0, 1] : List (Fin 4)) [2, 3, 1, 0]

#eval inv ([2, 3, 0, 1] : List (Fin 4))

#eval (finRange 4).permutations.product (finRange 4).permutations
  -- |>.map (fun (l1, l2) ↦ comp l1 (inv l2))
  |>.filter (fun (l1, l2) ↦ comp l1 (inv l2) = [2, 1, 3, 0])
  -- |>.length

-- [1, 0, 2, 3], [0, 1, 3, 2]

def a : List (List (Fin 4)) := [[1, 0, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3]]

-- 3
#eval (finRange 4).permutations
  |>.product ((finRange 4).permutations.product (finRange 4).permutations)
  |>.filter (fun (l1, l2, l3) ↦ comp l1 (inv l2) ∈ a ∧ comp l2 (inv l3) ∈ a ∧ comp l3 (inv l1) ∈ a ∧ [l1, l2, l3].Nodup)

def test3 (a : List (List (Fin 4))) : Bool :=
  ((finRange 4).permutations
  |>.product ((finRange 4).permutations.product (finRange 4).permutations)
  |>.filter (fun (l1, l2, l3) ↦ comp l1 (inv l2) ∈ a ∧ comp l2 (inv l3) ∈ a ∧ comp l3 (inv l1) ∈ a ∧ [l1, l2, l3].Nodup)
  |>.length) = 0

-- 4
#eval (finRange 4).permutations
  |>.product ((finRange 4).permutations.product ((finRange 4).permutations.product (finRange 4).permutations))
  |>.filter (fun (l1, l2, l3, l4) ↦ comp l1 (inv l2) ∈ a ∧ comp l2 (inv l3) ∈ a ∧ comp l3 (inv l4) ∈ a ∧ comp l4 (inv l1) ∈ a ∧ [l1, l2, l3, l4].Nodup)

def test4 (a : List (List (Fin 4))) : Bool :=
  ((finRange 4).permutations
  |>.product ((finRange 4).permutations.product ((finRange 4).permutations.product (finRange 4).permutations))
  |>.filter (fun (l1, l2, l3, l4) ↦ comp l1 (inv l2) ∈ a ∧ comp l2 (inv l3) ∈ a ∧ comp l3 (inv l4) ∈ a ∧ comp l4 (inv l1) ∈ a ∧ [l1, l2, l3, l4].Nodup)
  |>.length) = 0

#eval (finRange 4).permutations.product (finRange 4).permutations
  |>.map (fun (l1, l2) ↦ [l1, l2, [1, 0, 2, 3]])
  |>.filter (fun l ↦ l.Nodup ∧ ([0, 1, 2, 3] : List (Fin 4)) ∉ l ∧
    l.Sorted (fun x y ↦ (x.enum.map (fun i ↦ i.1 * i.2.val)).sum < (y.enum.map (fun i ↦ i.1 * i.2.val)).sum))
  |>.filter test3
  |>.filter test4
  -- |>.length

/-
Tier 0: I would be surprised if Peter didn't taught this (or some version of it) in the course.
rfl
rintro x ⟨y, hy⟩  : 'intro', but better
obtain ⟨y, hy⟩ := h x : 'have'/'cases'/'rcases', but better
have : worse 'obtain' but you can leave the name unspecified and it will be filled in as 'this'
refine ⟨x, ?_⟩ : 'exact', but better
apply : 'refine', but I can't be bothered to put all the '?_'s in
rw
induction
by_cases
simp : God-sent


Tier 1: not essential but very useful
exact? : stupid Mathlib search but no need to think about what I want to search for
simp? : source of all the 'simp only ...' which is preferred over 'simp'
simp_all/simp_all? : 'simp' but for everything
apply_fun : apply a function to both sides of the equation
congr/gcongr : opposite of 'apply_fun'
ext
match
norm_num/norm_cast : simp for numbers
split : splits cases for if-then-else or match
suffices
wlog

Tier 2: Occasionally useful
by_contra' : 'by_contra', but does 'push_neg' automatically
contrapose
convert : 'refine', but Lean's typesystem is annoying you
assumption : 'exact h', but you can't be bothered to find 'h'
change : change a thing via 'rfl'
choose : sometime Lean complains when using 'rcases' and 'obtain' to get an element out from ∃, this is a fix
fin_cases/interval_cases/mod_cases : super 'cases' for fin/intervals
infer_instance : magic tactic for instances
nth_rewrite : 'rw' but for the n-th occurence
decide : proof by computation

Tier 3: nice to have
clear : get rid of some the hypotheses
conv
calc : some people really like it but it is not how I do math
revert : opposite of 'intro'
subst h : 'rw [h] at *'
tauto
exfalso = 'apply False.elim'
use = 'refine ⟨ x, ?_ ⟩'
constructor = 'refine ⟨ ?_, ?_ ⟩'
left/right : 'apply Or.inl/Or.inr'
rename/rename_i : rename a hypothesis
rwa/simpa : 'rw'/'simp' followed by 'assumption'
specialize h x: 'obtain h := h x'
<;> : apply the next tactic to all the child goals of the first.
-/

instance instPropPreOrder {α : Type*}: PartialOrder (α → Prop) := by exact Pi.partialOrder
