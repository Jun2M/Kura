import Mathlib.Data.Sym.Sym2
import Kura.Graph.Defs


namespace Sym2
variable {α : Type u} [DecidableEq α] {p : α → Prop} [DecidablePred p]

/-
Bipartite Problem: Given e : E in a bipartite graph G with vertex set V = V₁ ∪ V₂,
  Without checking every vertex in V₁, return a vertex v in V₁ such that e is incident to v.
-/

def Distinguish (p : α → Prop) [DecidablePred p] : (Sym2 α) → Prop :=
  fun s => Multiset.card (s.toMultiset.filter p) = 1

instance Distinguish_decidable (p : α → Prop) [DecidablePred p] : DecidablePred (Distinguish p) :=
  sorry

def mem_distinguishables_iff (a b : α) : Distinguish p s(a, b) ↔ p a ≠ p b := by
  simp only [Distinguish, toMultiset_eq, Multiset.insert_eq_cons, Multiset.card_eq_one, ne_eq,
    eq_iff_iff]
  by_cases ha : p a <;> by_cases hb : p b <;> simp [ha, hb, Multiset.filter_singleton]
  intro x
  apply Multiset.ne_of_card_ne
  simp only [Multiset.card_cons, Multiset.card_singleton, Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_one,
    not_false_eq_true]

end Sym2

namespace edge
variable {α : Type u} [LinearOrder α] {p : α → Prop} [DecidablePred p]


def Distinguish (p : α → Prop) [DecidablePred p] : edge α → Prop
| dir (some a, some b) => p a ≠ p b
| undir s => Sym2.Distinguish p s
| _ => true

end edge

namespace Graph
variable {V E : Type*} [LinearOrder V] [DecidableEq E] (G : Graph V E) (u v : V)

class Bipartite where
  L : Set V
  hLDec : DecidablePred (· ∈ L)
  distinguishes : ∀ e, (G.inc e).Distinguish (· ∈ L)
