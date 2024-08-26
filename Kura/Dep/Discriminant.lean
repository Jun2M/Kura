import Mathlib.Data.Sym.Sym2


namespace Sym2
variable {α : Type u} [DecidableEq α] {p : α → Prop} [DecidablePred p]

def Discriminant (s : Sym2 α) : Bool :=
  Multiset.card (equivMultiset _ s
  |>.val
  |>.filter p) = 1
