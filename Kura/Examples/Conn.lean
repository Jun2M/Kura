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
