import Mathlib.Data.Sym.Sym2.Order

open List
variable {α : Type*}

def List.Vector.singletonEquiv {α : Type*} : List.Vector α 1 ≃ α where
  toFun := (·.head)
  invFun := (⟨[·], rfl⟩)
  left_inv v := by
    apply Vector.eq
    simp only [toList_singleton, cons.injEq, and_true]
    rfl
  right_inv := fun a => rfl

@[simp]
lemma List.Vector.singletonEquiv_apply (v : List.Vector α 1) :
    List.Vector.singletonEquiv v = v.head :=
  match v with
  | ⟨_, _⟩ => rfl

@[simp]
lemma List.Vector.singletonEquiv_mem (v : List.Vector α 1) :
    List.Vector.singletonEquiv v ∈ v.toList := by
  simp only [toList_singleton, singletonEquiv_apply, mem_cons, not_mem_nil, or_false]

def Sym.Sym'.singletonEquiv (s : Sym.Sym' α 1) : α :=
  Quot.lift List.Vector.singletonEquiv (fun u v h ↦ by
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp u.prop
    obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp v.prop
    simp only [Setoid.r, Function.onFun, Setoid.r, hx, hy, List.perm_singleton, List.cons.injEq,
      and_true] at h
    subst y
    simp only [Vector.singletonEquiv, Equiv.coe_fn_mk]
    congr
    rw [← Subtype.val_injective.eq_iff, hx, hy]) s

@[simp]
lemma Sym.oneEquiv_symm_apply (a : α) : Sym.oneEquiv.symm ⟨{a}, rfl⟩ = a := rfl

-- lemma Sym.apply_oneEquiv_symm_comm {α : Type u} (s : Sym α 1) (f : α → β) :
--     f (Sym.oneEquiv.symm s) = Sym.oneEquiv.symm (s.map f) := by
--   sorry

def Sym2.ofIsDiag (s : Sym2 α) (hs : s.IsDiag) : α :=
  Sym2.rec (motive := fun (s : Sym2 α) ↦ s.IsDiag → α) (fun p _hp ↦ p.1) (by
  rintro p q h
  ext hDiag
  rw [rel_iff'] at h
  obtain rfl | h := h
  · rfl
  · subst p
    obtain ⟨q1, q2⟩ := q
    simp only [isDiag_iff_proj_eq] at hDiag
    subst q2
    rfl) s hs

@[simp]
lemma Sym2.ofIsDiag_pair {a : α} : Sym2.ofIsDiag s(a, a) (by rfl) = a := rfl

lemma Sym2.ofIsDiag_mem (s : Sym2 α) (hs : s.IsDiag) : Sym2.ofIsDiag s hs ∈ s := by
  induction' s with a b
  simp only [isDiag_iff_proj_eq] at hs
  subst b
  simp only [ofIsDiag_pair, mem_iff, or_self]

@[simp]
lemma Sym2.eq_ofIsDiag (s : Sym2 α) (hs : s.IsDiag) : s(s.ofIsDiag hs, s.ofIsDiag hs) = s := by
  induction' s with a b
  simp only [isDiag_iff_proj_eq] at hs
  subst b
  rfl

def Multiset.singletonEquiv (s : Multiset α) (h : Multiset.card s = 1) : α :=
  Sym.oneEquiv.symm ⟨s, h⟩

@[simp]
lemma Multiset.singletonEquiv_cancel (s : Multiset α) (h : Multiset.card s = 1) :
    {Multiset.singletonEquiv s h} = s := by
  change Sym.oneEquiv (Sym.oneEquiv.symm ⟨s, h⟩) = s
  simp only [Equiv.apply_symm_apply, Sym.coe_mk]

lemma Multiset.singletonEquiv_mem (s : Multiset α) (h : Multiset.card s = 1) :
    Multiset.singletonEquiv s h ∈ s := by
  have : Multiset.singletonEquiv s h ∈ ({Multiset.singletonEquiv s h} : Multiset _) := by
    rw [mem_singleton]
  convert this
  exact Eq.symm (singletonEquiv_cancel s h)

def Finset.singletonEquiv (s : Finset α) (h : s.card = 1) : α :=
  Multiset.singletonEquiv s.val h

lemma Finset.singletonEquiv_mem (s : Finset α) (h : s.card = 1) :
    Finset.singletonEquiv s h ∈ s := by
  simp only [singletonEquiv]
  exact Multiset.singletonEquiv_mem s.val h
