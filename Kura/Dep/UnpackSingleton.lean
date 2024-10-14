import Mathlib.Data.Sym.Sym2.Order


def Vector.unpackSingleton {α : Type u} (v : Mathlib.Vector α 1) : α :=
  v.get ⟨0, Nat.zero_lt_succ 0⟩

def Sym.Sym'.unpackSingleton {α : Type u} (s : Sym.Sym' α 1) : α :=
  Quot.lift Vector.unpackSingleton (fun u v h ↦ by
    simp only [Vector.unpackSingleton, Fin.zero_eta, Fin.isValue, Mathlib.Vector.get_zero]
    obtain ⟨x, hx⟩ := List.length_eq_one.mp u.prop
    obtain ⟨y, hy⟩ := List.length_eq_one.mp v.prop
    have : u = v := by
      simp only [Setoid.r, Function.onFun, Setoid.Rel, hx, hy, List.perm_singleton, List.cons.injEq,
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

def Finset.unpackSingleton {α : Type u} (s : Finset α) (h : s.card = 1) : α :=
  Multiset.unpackSingleton s.val h
