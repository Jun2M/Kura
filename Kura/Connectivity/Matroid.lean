import Kura.Connectivity.Tree
import Mathlib.Data.Matroid.Dual

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] (G : Graph V E)


def IndepMatroidOfFintype [Fintype V] [Fintype E] [Undirected G] : IndepMatroid E := by
  refine IndepMatroid.ofFinite Set.finite_univ (fun A => G{A}ᴳ.acyclic) ?_ ?_ ?_ ?_
  · intro n
    by_contra! h
    simp only [not_isEmpty_iff] at h
    obtain ⟨⟨fv, fe, hcomm⟩, hfᵥinj, hfₑinj⟩ := h
    obtain x := fe 0
    apply IsEmpty.elim' _ x
    simp only [Set.isEmpty_coe_sort]
  · rintro A B hB hsu n
    contrapose! hB
    simp only [not_isEmpty_iff] at hB
    obtain ⟨SubG⟩ := hB
    simp only [acyclic, not_forall, not_isEmpty_iff]
    use n
    refine ⟨?_⟩
    apply SubG.trans
    apply (Es_spanningsubgraph_Es_of_subset _ hsu).toSubgraphOf
  · rintro A B hAIndep hBIndep hAltB
    have hA := (G.Es A).n_eq_m_add_c_of_acyclic hAIndep
    have hB := (G.Es B).n_eq_m_add_c_of_acyclic hBIndep
    rw [ncard_eq_card A, ncard_eq_card B] at hAltB
    have hBNCltANC : (G.Es B).NumberOfComponents < (G.Es A).NumberOfComponents := by omega
    clear hA hB hAltB
    unfold NumberOfComponents at hBNCltANC
    have : ¬ (G.Es B).connSetoid ≤ (G.Es A).connSetoid := by
      apply not_imp_not.mpr (Quotient.card_quotient_le_card_quotient_of_ge)
      convert hBNCltANC.not_le
    simp only [Setoid.le_def, not_forall, Classical.not_imp] at this; clear hBNCltANC
    obtain ⟨v, w, hvw, hvw'⟩ := this
    simp only [connSetoid] at hvw hvw'
    obtain ⟨n, S, hSstart, hSfinish⟩ := hvw.PathSubgraphOf
    let i := Fin.find (fun x => ¬ (G.Es A).conn v (S.fᵥ x)) |>.get (Fin.isSome_find_iff.mpr
      ⟨Fin.last n, by rwa [hSfinish]⟩)
    have himem : i ∈ Fin.find (fun x => ¬ (G.Es A).conn v (S.fᵥ x)) := Option.get_mem _
    have hspec : ¬ (G.Es A).conn v (S.fᵥ i) := by
      apply Fin.find_spec (fun x => ¬ (G.Es A).conn v (S.fᵥ x)) himem
    have hine0 : i ≠ 0 := by
      intro h
      rw [h, hSstart] at hspec
      exact hspec (conn.refl _ _)
    let iₑ := i.pred hine0
    let ipred := iₑ.castSucc
    have hipredconn : (G.Es A).conn v (S.fᵥ ipred) := by
      have := Fin.find_min himem (Fin.castSucc_pred_lt hine0 : ipred < i)
      simpa only [Decidable.not_not] using this
    have : (PathGraph n).canGo ipred iₑ i = true := by
      convert PathGraph.canGo' iₑ
      exact (i.succ_pred hine0).symm
    use S.fₑ iₑ, (S.fₑ iₑ).prop
    constructor
    · contrapose! hspec
      apply Relation.ReflTransGen.tail hipredconn
      use ⟨S.fₑ iₑ, hspec⟩
      rw [← (Es_spanningsubgraph G A).toSubgraphOf.canGo_iff, Es_spanningsubgraph_fᵥ, id_eq, id_eq,
        Es_spanningsubgraph_fₑ]
      exact (Es_spanningsubgraph G B).toSubgraphOf.canGo <| S.canGo this
    · simp
      sorry
  · rintro A hAIndep
    simp only [Set.subset_univ]
  done
