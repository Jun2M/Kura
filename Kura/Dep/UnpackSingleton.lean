import Mathlib.Data.Sym.Sym2.Order


def List.Vector.unpackSingleton {α : Type u} (v : List.Vector α 1) : α :=
  v.get ⟨0, Nat.zero_lt_succ 0⟩

lemma List.Vector.unpackSingleton_eq {α : Type u} (v : List.Vector α 1) :
    List.Vector.unpackSingleton v = v.head := by
  match v with
  | ⟨[a], h⟩ => rfl

-- @[simp]
-- lemma List.Vector.unpackSingleton_mem {α : Type u} (v : List.Vector α 1) :
--     List.Vector.unpackSingleton v ∈ v := by
--   simp only [List.Vector.unpackSingleton, List.Vector.get]
--   exact List.Vector.mem_singleton_self _

def Sym.Sym'.unpackSingleton {α : Type u} (s : Sym.Sym' α 1) : α :=
  Quot.lift List.Vector.unpackSingleton (fun u v h ↦ by
    simp only [List.Vector.unpackSingleton, Fin.zero_eta, Fin.isValue, List.Vector.get_zero]
    obtain ⟨x, hx⟩ := List.length_eq_one.mp u.prop
    obtain ⟨y, hy⟩ := List.length_eq_one.mp v.prop
    have : u = v := by
      simp only [Setoid.r, Function.onFun, Setoid.r, hx, hy, List.perm_singleton, List.cons.injEq,
        and_true] at h
      subst h
      apply_fun Subtype.val using Subtype.val_injective
      rw [hx, hy]
    subst this
    rfl) s

@[simp]
lemma Sym.oneEquiv_symm_apply {α : Type u} (a : α) : Sym.oneEquiv.symm ⟨{a}, rfl⟩ = a := rfl

lemma Sym.apply_oneEquiv_symm_comm {α : Type u} (s : Sym α 1) (f : α → β) :
    f (Sym.oneEquiv.symm s) = Sym.oneEquiv.symm (s.map f) := by
  sorry

def Multiset.unpackSingleton {α : Type u} (s : Multiset α) (h : Multiset.card s = 1) : α :=
  Sym.oneEquiv.symm ⟨s, h⟩

@[simp]
lemma Multiset.unpackSingleton_cancel {α : Type u} (s : Multiset α) (h : Multiset.card s = 1) :
    {Multiset.unpackSingleton s h} = s := by
  change Sym.oneEquiv (Sym.oneEquiv.symm ⟨s, h⟩) = s
  simp only [Equiv.apply_symm_apply, Sym.coe_mk]

lemma Multiset.unpackSingleton_mem {α : Type u} (s : Multiset α) (h : Multiset.card s = 1) :
    Multiset.unpackSingleton s h ∈ s := by
  have : Multiset.unpackSingleton s h ∈ ({Multiset.unpackSingleton s h} : Multiset _) := by
    rw [mem_singleton]
  convert this
  exact Eq.symm (unpackSingleton_cancel s h)

def Finset.unpackSingleton {α : Type u} (s : Finset α) (h : s.card = 1) : α :=
  Multiset.unpackSingleton s.val h

lemma Finset.unpackSingleton_mem {α : Type u} (s : Finset α) (h : s.card = 1) :
    Finset.unpackSingleton s h ∈ s := by
  simp only [unpackSingleton]
  exact Multiset.unpackSingleton_mem s.val h
