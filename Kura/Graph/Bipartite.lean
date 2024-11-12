import Mathlib.Data.Sym.Sym2
import Kura.Graph.Defs


namespace Sym2
variable {α : Type u} {p : α → Prop}

/-
Bipartite Problem: Given e : E in a bipartite graph G with vertex set V = V₁ ∪ V₂,
  Without checking every vertex in V₁, return a vertex v in V₁ such that e is incident to v.
-/

def Distinguish (p : α → Prop) : (Sym2 α) → Prop := by
  apply Quot.rec
  on_goal 2 => exact (fun x ↦ p x.1 ≠ p x.2)
  rintro a b r
  simp only [rel_iff'] at r
  obtain (rfl | rfl) := r
  · rfl
  · simp only [Prod.fst_swap, Prod.snd_swap, ne_eq, eq_iff_iff, eq_rec_constant]
    tauto

@[simp]
lemma distinguish_pair_iff (a b : α) : Distinguish p s(a, b) ↔ p a ≠ p b := by
  simp only [Distinguish, ne_eq, eq_iff_iff]

-- instance Distinguish_decidable (p : α → Prop) [DecidablePred p] : DecidablePred (Distinguish p) := by
  -- rintro s
  -- refine decidable_of_iff (Distinguish p s)
  -- sorry

end Sym2

namespace edge
variable {α : Type u} {p : α → Prop}


def Distinguish (p : α → Prop) : edge α → Prop
| dir (some a, some b) => p a ≠ p b
| undir s => Sym2.Distinguish p s
| _ => False

end edge

namespace Graph
variable {V E : Type*} [DecidableEq V] (G : Graph V E) (u v : V)

class Bipartite where
  L : Set V
  distinguishes : ∀ e, (G.inc e).Distinguish (· ∈ L)
