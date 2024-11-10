import Kura.Examples.Defs
import Kura.Conn.Conn

namespace Graph
open edge
variable {V W E F : Type*} (G : Graph V E) (e : E) (u v w : V)


instance instEdgelessGraphConnected (n : ℕ) [Fact (n < 2)] : (EdgelessGraph n).connected where
  all_conn u v := by have : n < 2 := Fact.out; interval_cases n <;> rw [Subsingleton.allEq u v] <;>
    apply conn_refl

lemma EdgelessGraph_not_connected (n : ℕ) (hn : 2 ≤ n) : ¬ (EdgelessGraph n).connected := by
  intro h
  obtain ⟨u, v, huv⟩ := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨P, rfl, rfl⟩ := (h.all_conn u v).path
  by_cases hPlen : P.length = 0
  · rw [P.length_zero_iff_eq_nil] at hPlen
    rw [hPlen] at huv
    simp only [Path.nil_start, Path.nil_finish, ne_eq, not_true_eq_false] at huv
  · obtain e := P.edges.head ((Walk.length_ne_zero_iff_edges_ne_nil P.toWalk).mp hPlen)
    exact e.elim


instance instCompleteGraphConnected (n : ℕ) : (CompleteGraph n).connected := by
  sorry

instance instCompleteBipGraphConnected (n₁ n₂ : ℕ+) : (CompleteBipGraph n₁ n₂).connected := by
  sorry

lemma PathGraph_conn_0 (n : ℕ+) (v : Fin n) : (PathGraph n).conn 0 v := by
  induction' v with j hjpos
  induction' j with x ih
  · exact conn_refl (PathGraph n) 0
  · by_cases h : x +1 = n
    · sorry
    · have hxlt : x+1 < n := by omega
      specialize ih (by omega)
      apply ih.tail ; clear ih
      use x
      simp only [canGo, PathGraph, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Nat.cast_add,
        Nat.cast_one, canGo_iff_eq_of_undir, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk]
      refine Or.inl ?_
      refine ⟨?_, ?_⟩
      · sorry
      · sorry
