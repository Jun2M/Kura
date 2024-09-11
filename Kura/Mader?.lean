import Kura.Finite
import Kura.Dep.BigOperator

namespace Graph
open edge
variable {V E : Type*} [DecidableEq V]


theorem Mader {t : ℕ+} (G : Graph V E) [simple G] [Fintype V] [Fintype E]
  (hminor : ¬ G.hasMinor (Complete (Fin t))) :
  let n := Fintype.card V
  let m := Fintype.card E
  m ≤ (2^t.natPred - 1) * n := by
  intro n m
  induction t using PNat.recOn generalizing V E G with
  | p1 =>
    have hn : n = 0 := sorry
    have hm : m = 0 := sorry
    rw [hm]
    exact Nat.zero_le _
  | hp t iht =>
  match h : m with
  | 0 => exact Nat.zero_le _
  | m' + 1 =>

      induction n using Nat.strong_induction_on generalizing V E G with
      | _ _ =>
        by_contra! h
        rename_i n'' ihn _ _ _ _
        unfold_let at h
        have : Nonempty E := by
          rw [← Fintype.card_pos_iff]
          sorry

        obtain e := @Classical.ofNonempty _ this
        obtain ⟨v, hv⟩ := exist_mem G e

        let H_ : InducedSubgraph G := ⟨G.neighbourhood v⟩
        let H := H_.eval
        have hHt : ¬ H.hasMinor (Complete (Fin t)) := sorry
        have hHsimple : simple H := sorry
        let hvfin : Fintype ↑(H_.rmvᶜ) := sorry
        let hefin : Fintype { e // ∀ v_1 ∈ G.inc e, v_1 ∉ G.neighbourhood v } := sorry
        obtain a := @iht _ _ _ H hHsimple hvfin sorry hHt
        simp only at a
        rw [Fintype.card_eq_sum_ones] at a
        sorry 
