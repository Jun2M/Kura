import Mathlib.Data.Sym.Sym2
import Kura.Graph.Defs


namespace Sym2
variable {α : Type u} [DecidableEq α] {p : α → Prop} [DecidablePred p]

/-
Bipartite Problem: Given e : E in a bipartite graph G with vertex set V = V₁ ∪ V₂,
  Without checking every vertex in V₁, return a vertex v in V₁ such that e is incident to v.
-/

def Distinguishables (p : α → Prop) [DecidablePred p] : Set (Sym2 α) :=
  {s | Multiset.card (s.toMultiset.filter p) = 1}

def mem_distinguishables_iff (a b : α) : s(a, b) ∈ Distinguishables p ↔ p a ≠ p b := by
  simp only [Distinguishables, Multiset.card_eq_one, Set.mem_setOf_eq, toMultiset_eq,
    Multiset.insert_eq_cons, ne_eq, eq_iff_iff]
  by_cases ha : p a <;> by_cases hb : p b <;> simp [ha, hb, Multiset.filter_singleton]
  intro x
  apply Multiset.ne_of_card_ne
  simp only [Multiset.card_cons, Multiset.card_singleton, Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_one,
    not_false_eq_true]


