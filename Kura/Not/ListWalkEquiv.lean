import Mathlib.Combinatorics.SimpleGraph.Connectivity
import «Kuratowski».List


structure WalkL {V : Type*} (G : SimpleGraph V) (v w : V) where
  L : List V
  Nonempty_L : L ≠ []
  From : L.head Nonempty_L = v
  To : L.getLast Nonempty_L = w
  Adj : L.Chain' G.Adj


class ListLike (L : Type u) (a : outParam (Type*)) where
  coe : L → List a
  coe_injective : Function.Injective coe


instance {V : Type*} {G : SimpleGraph V} {v w : V} : ListLike (WalkL G v w) V where
  coe := WalkL.L
  coe_injective := by
    intro l₁ l₂ h
    cases l₁
    cases l₂
    simp_all


-- def Wal (n : ℕ) : {a : List Nat // ∃ (h : a ≠ []), a.head h = n} := sorry


def SimpleGraph.Walk.toList {V : Type} {v w : V} {G : SimpleGraph V} (W : G.Walk v w) :
  WalkL G v w :=
  match W with
  | SimpleGraph.Walk.nil => by
    apply WalkL.mk [v]
    <;> simp

  | @SimpleGraph.Walk.cons' _ _ a b c habAdj W' =>
    let ⟨l, h, f, t, adj⟩ := SimpleGraph.Walk.toList W'
    ⟨ a :: l, by simp, by simp, by simp [h, t], by
      rw [← List.cons_head_tail l h]
      exact List.Chain'.cons (f ▸ habAdj) (by simp [adj])
    ⟩


def SimpleGraph.Walk.fromList {V : Type} {v w : V} {G : SimpleGraph V} (l : WalkL G v w) :
  G.Walk v w := by
    rcases l with ⟨l, h, f, t, adj⟩
    match l with
    | [] =>
      absurd h
      rfl

    | [a] =>
      simp at f t
      subst w a
      exact SimpleGraph.Walk.nil

    | a :: b :: l' =>
      simp at f
      subst a
      rw [List.chain'_cons] at adj
      apply SimpleGraph.Walk.cons adj.1
      exact SimpleGraph.Walk.fromList ⟨b :: l', List.cons_ne_nil b l',
        rfl, by rwa [List.getLast_cons (by simp)] at t, adj.2 ⟩
    done
