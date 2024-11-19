import Mathlib.Logic.Equiv.Set

namespace Equiv
variable {α : Type*} {s t : Set α}

@[simp]
lemma setCongr_symm (h : s = t) : (Equiv.setCongr h).symm = Equiv.setCongr h.symm := rfl

end Equiv
