import Mathlib.Combinatorics.SimpleGraph.Partition
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic


open SimpleGraph Mathlib
theorem exercise4 (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (k : ℕ+)
  (d : Fin k → ℕ) (hd : G.maxDegree +1 -k ≤ ∑ i, d i) :
    ∃ (P : Fin k → (Finset V)), (List.ofFn P).Pairwise (Disjoint · ·) ∧
      (List.ofFn P).foldl (· ∪ ·) ∅ = Finset.univ ∧
      ∀ i : Fin k, (G.induce (P i)).maxDegree ≤ d i  := by
  induction k using PNat.recOn generalizing V G with
  | p1 =>
    use ![Finset.univ]
    refine ⟨?_, ?_, ?_⟩
    · simp
    · simp
    · intro i
      fin_cases i
      simp at hd ⊢
      convert hd using 2
      sorry
  | hp k' IH =>
    suffices h : ∃ V0 : Finset V, (G.induce V0).maxDegree ≤ d 0 ∧
      (G.induce V0ᶜ).maxDegree ≤ G.maxDegree - 1 - k' by
      rcases h with ⟨V0, h1, h2⟩
      rcases IH (G.induce (V0ᶜ : Finset V)) (λ i => d i.succ) ?_ with ⟨P, hP1, hP2, hP3⟩
      let P' := λ i => (P i).map (Function.Embedding.subtype (· ∈ V0ᶜ))
      use Fin.cons V0 P'
      refine ⟨?_, ?_, ?_⟩
      · simp
        refine ⟨?_, ?_⟩
        · intro j
          unfold_let
          rw [Finset.disjoint_left]
          intro v hv hvv
          simp at hvv
          rcases hvv with ⟨hun, hmem⟩
          exact hun hv
        · intro j₁ j₂ hne
          simp at hP1
          specialize hP1 hne
          unfold_let
          rw [Finset.disjoint_left] at hP1 ⊢
          intro v hv hvv
          simp at hv hvv
          rcases hv with ⟨hvn₁, hmem₁⟩
          rcases hvv with ⟨hvn₂, hmem₂⟩
          exact False.elim (hP1 hmem₁ hmem₂)

      · simp [-Finset.empty_union]
        simp_rw [Finset.union_comm ∅ V0]
        rw [List.foldl_assoc (op := (· ∪ ·)) (ha := Finset.instAssociativeUnion)]
        unfold_let
        simp
        simp_rw [← Function.comp_def]
        rw [← List.map_ofFn, ← Finset.map_empty _, List.foldl_map' _ _, hP2, ← Finset.attach_eq_univ, Finset.attach_map_val (s := V0ᶜ)]
        simp
        intro x y
        ext v
        simp
        exact exists_or.symm
      · intro i
        unfold_let
        simp
        refine ⟨?_, ?_⟩
        · rw [← G.induce_eq_induce']
          exact h1
        · rw [← G.induce_eq_induce']
          exact h2


    sorry
