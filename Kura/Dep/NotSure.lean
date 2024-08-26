-- import Mathlib
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic


def Fin0To (α : Type*) : Fin 0 → α := by
  rintro ⟨n, h⟩
  absurd h
  exact Nat.not_lt_zero n

@[simp]
theorem Option.get_map{α : Type u_1} {β : Type u_2} (f : α → β)
  (o : Option α) (homap : isSome (Option.map f o)) (ho : isSome o) :
  Option.get (Option.map f o) homap = f (Option.get o ho) := by
  match o with
  | none => simp at ho
  | some x => simp
  done

-- instance Fin.instCanLiftFinFinCoeLt {n m : ℕ} (h : m < n) :
--   CanLift (Fin n) (Fin m) ((↑) : Fin m → Fin n) where
--   coe := Fin.castLt h
--   cond := fun x => x.val < m
--   prf := by
--     intro x
--     exact x.property
--   inv := fun x => ⟨x.val, x.property⟩

class gSetLike (T : Type u → Type u) : Type (u+1) where
  coe : ∀ α : Type u, T α → Set α
  coe_injective : ∀ {α}, Function.Injective (coe α)

instance Sym2.gSetLike : gSetLike Sym2 where
  coe := λ α => SetLike.coe
  coe_injective := by
    intro α x y
    rw [SetLike.coe_set_eq]
    tauto
    done

instance Set.gSetLike : gSetLike Set where
  coe := λ α => id
  coe_injective := by
    intro α x y
    tauto
    done

instance gSetLike.SetLike {T : Type → Type} [gSetLike T] : SetLike (T α) α where
  coe := gSetLike.coe α
  coe_injective' := gSetLike.coe_injective
