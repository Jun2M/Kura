import Kura.Connectivity.Tree
import Mathlib.Data.Matroid.Dual
import Matroid.Axioms.Circuit

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] (G : Graph V E) [DecidableEq E]


def CircuitMatroid [Undirected G] : FinsetCircuitMatroid E where
  E := Set.univ
  IsCircuit C := ∃ (Cyc : G.Cycle), Cyc.edges.toFinset = C
  empty_not_isCircuit := by
    simp only [List.toFinset_eq_empty_iff, not_exists]
    rintro Cyc
    simp only [Walk.edges, List.map_eq_nil_iff, ne_eq]
    exact Cyc.stepsNeNil
  circuit_antichain := by
    simp only [IsAntichain, Set.Pairwise, Set.mem_setOf_eq, ne_eq, Pi.compl_apply, compl_iff_not,
      forall_exists_index, forall_apply_eq_imp_iff]
    rintro Cyc1 Cyc2 hne hsub
    have hssub : Cyc1.edges.toFinset ⊂ Cyc2.edges.toFinset :=
      HasSubset.Subset.ssubset_of_ne hsub hne
    clear hsub hne
    have ⟨H1, H2⟩ := hssub
    rw [Finset.ssubset_iff_exists_cons_subset] at hssub
    obtain ⟨e, he, hsu⟩ := hssub
    have hemem2 : e ∈ Cyc2.edges := by
      simp only [Finset.cons_eq_insert, Finset.insert_subset_iff, List.mem_toFinset] at hsu
      exact hsu.1
    obtain ⟨iₑ, hiₑle, hiₑ⟩ := List.getElem_of_mem hemem2
    let G₁ := (Cyc1.CycleGraph_Emb).toHom.range
    let G₂ := (Cyc2.CycleGraph_Emb).toHom.range
    let G₂' := G.toSubgraph G₂.Sᵥ (G₂.Sₑ \ {e}) ?_

    have hG₁' : G₁ ≤ G₂' := by
      rw [Subgraph.le_iff]
      constructor
      · unfold G₂'
        rw [toSubgraph_val_Sᵥ]
        sorry
      · unfold G₂' G₂ G₁
        rw [toSubgraph_val_Sₑ, Set.subset_diff_singleton_iff]
        simp only [Cycle.CycleGraph_Emb, Closed.exist_CycleGraph_Hom, Hom.range_Sₑ, Set.mem_range,
          not_exists]
        constructor
        · rintro f hf
          simp only [Set.mem_range] at hf ⊢
          obtain ⟨y, rfl⟩ := hf
          specialize H1 (by simp only [Fin.getElem_fin, List.mem_toFinset, List.getElem_mem]: Cyc1.edges[y] ∈ _)
          simp only [Fin.getElem_fin, List.mem_toFinset] at H1
          obtain ⟨z, hzlt, hz⟩ := List.getElem_of_mem H1
          use z
          convert hz
          simp only [Walk.edges_length] at hzlt
          rw [Fin.val_natCast, Nat.mod_eq_of_lt hzlt]
        · rintro x rfl
          simp only [List.mem_toFinset, List.getElem_mem, not_true_eq_false] at he

    apply ((PathGraph_acyclic (Cyc2.length-1)) Cyc1.length inferInstance).false
    refine Emb.trans (?_) (CycleGraph_Subgraph_singleton_comple_Isom_PathGraph Cyc2.length iₑ).toEmb
    refine (Cycle.CycleGraph_Emb G Cyc1).range_Isom.toEmb.trans ?_
    refine (Subgraph.Emb_of_le hG₁').trans ?_
    refine Emb.trans (?_ : Emb _ ((CycleGraph Cyc2.length).Es {↑iₑ}ᶜ).val)
      (((CycleGraph Cyc2.length).Es {↑iₑ}ᶜ).toGraph_Isom_toGraph).toEmb
    have := Subgraph.Emb_of_Emb_le ((Cycle.CycleGraph_Emb G Cyc2).range_Isom).symm.toEmb

    sorry
    sorry
  circuit_elimination C₁ C₂ e hC₁ hC₂ hne hmemInter := by
    obtain ⟨Cyc₁, rfl⟩ := hC₁
    obtain ⟨Cyc₂, rfl⟩ := hC₂
    sorry
  circuit_subset_ground _ _ _ _ := by trivial
  Indep := sorry
  indep_iff := sorry

-- def IndepMatroidofFinitary [Undirected G] : IndepMatroid E := by
--   refine IndepMatroid.ofFinitary Set.univ (fun A => G{A}ᴳ.acyclic) ?_ ?_ ?_ ?_ ?_
--   · refine acyclic_of_IsEmpty_E
--   · rintro A B hBacyc hsu
--     refine (G.Es_spanningsubgraph_Es_of_subset hsu).acyclic hBacyc
--   · rintro A B hAacyc hBMax ⟨hBacyc, hAUB⟩
--     simp only [Maximal, hAacyc, Set.le_eq_subset, true_and, not_forall, Classical.not_imp] at hBMax
--     obtain ⟨C, hC, hCsub, hnsubC⟩ := hBMax

--     have : ¬ Relation.ReflTransGen (G.Es B).adj ≤ Relation.ReflTransGen (G.Es A).adj := by
--       intro h
--       sorry
--       -- acyclic_of_Es_acyclic_of_Es_subset
--     simp_rw [Pi.le_def, not_forall, le_Prop_eq, _root_.not_imp] at this
--     obtain ⟨v, w, (hvw : (G.Es B).conn v w), (hvw' : ¬ (G.Es A).conn v w)⟩ := this
--     obtain ⟨n, S, rfl, rfl⟩ := hvw.PathEmb
--     have : DecidablePred fun x => ¬ (G.Es A).conn (S.fᵥ 0) (S.fᵥ x) := Classical.decPred _
--     let i := Fin.find (fun x => ¬ (G.Es A).conn (S.fᵥ 0) (S.fᵥ x)) |>.get (Fin.isSome_find_iff.mpr
--       ⟨Fin.last n, hvw'⟩)
--     have himem : i ∈ Fin.find (fun x => ¬ (G.Es A).conn (S.fᵥ 0) (S.fᵥ x)) := Option.get_mem _
--     have hspec : ¬ (G.Es A).conn (S.fᵥ 0) (S.fᵥ i) :=
--       Fin.find_spec (fun x => ¬ (G.Es A).conn (S.fᵥ 0) (S.fᵥ x)) himem
--     have hine0 : i ≠ 0 := fun h => (h ▸ hspec) (conn.refl _ _)
--     let iₑ := i.pred hine0
--     let ipred := iₑ.castSucc
--     have hipredconn : (G.Es A).conn (S.fᵥ 0) (S.fᵥ ipred) := by
--       have := Fin.find_min himem (Fin.castSucc_pred_lt hine0 : ipred < i)
--       simpa only [not_not] using this
--     have hinA : ↑(S.fₑ iₑ) ∉ A := by
--       contrapose! hspec
--       apply Relation.ReflTransGen.tail hipredconn
--       use ⟨S.fₑ iₑ, hspec⟩
--       rw [← (Es_spanningsubgraph G A).canGo_iff, Es_spanningsubgraph_fᵥ, id_eq, id_eq,
--         Es_spanningsubgraph_fₑ]
--       refine (Es_spanningsubgraph G B).canGo <| S.canGo ?_
--       convert PathGraph.canGo' iₑ
--       exact (i.succ_pred hine0).symm
--     use S.fₑ iₑ, (S.fₑ iₑ).prop, hinA
--     simp only
--     let S' := G.Es_of_Es_Es (insert (S.fₑ iₑ).val A) {⟨S.fₑ iₑ, Set.mem_insert (↑(S.fₑ iₑ)) A⟩}ᶜ (by
--       simp only [Set.image_val_compl, Set.image_singleton, Set.mem_singleton_iff,
--         Set.insert_diff_of_mem, Set.diff_singleton_eq_self hinA] : A = _)
--     rw [← get_not_conn'_iff_acyclic_of_Es_singleton_compl_acyclic
--       (S'.symm.acyclic hAacyc) (e := ⟨S.fₑ iₑ, Set.mem_insert (↑(S.fₑ iₑ)) A⟩)]
--     apply Function.mt (S'.symm.conn' (s := G.get _))
--     simp only [Es_of_Es_Es_symm_fᵥ, id_eq, Sym2.map_id', S']
--     let T := S.trans (Es_spanningsubgraph G _).toEmb
--     change ¬(G.Es A).conn' (G.get (T.fₑ iₑ))
--     rw [Hom.get, PathGraph_get, Sym2.map_pair_eq]
--     simp only [Emb.trans_fᵥ, Es_spanningsubgraph_fᵥ, Function.comp_apply, id_eq, T]
--     change ¬(G.Es A).conn' s(S.fᵥ ipred, S.fᵥ (i.pred _).succ)
--     rw [Fin.succ_pred, conn'_pair]
--     exact (hspec <| hipredconn.trans ·)
--   · rintro A hFinitary
--     contrapose! hFinitary
--     simp only [acyclic, not_forall, not_isEmpty_iff] at hFinitary
--     obtain ⟨n, ⟨S⟩⟩ := hFinitary
--     let B := Set.range S.fₑ
--     use Subtype.val '' Set.range S.fₑ, Subtype.coe_image_subset A (Set.range S.fₑ),
--       Set.toFinite (Subtype.val '' Set.range S.fₑ)
--     rw [not_acyclic_iff_cycle]
--     use n, ?_
--     refine {
--       fᵥ := S.fᵥ,
--       fₑ e := ⟨S.fₑ e, by simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and,
--           exists_apply_eq_apply]⟩,
--       inc := S.inc,
--       fᵥinj v w hvw := by simpa only [Fin.ext_iff', S.fᵥinj.eq_iff] using hvw
--       fₑinj e f hef := by rwa [Subtype.mk.injEq, Subtype.coe_inj, S.fₑinj.eq_iff] at hef
--     }
--   · rintro A hA a ha
--     trivial

-- def IndepMatroidOfFintype [Fintype V] [Fintype E] [Undirected G] : IndepMatroid E := by
--   refine IndepMatroid.ofFinite Set.finite_univ (fun A => G{A}ᴳ.acyclic) ?_ ?_ ?_ ?_
--   · intro n
--     by_contra! h
--     simp only [not_isEmpty_iff] at h
--     obtain ⟨⟨fv, fe, hcomm⟩, hfᵥinj, hfₑinj⟩ := h
--     obtain x := fe 0
--     apply IsEmpty.elim' _ x
--     simp only [Set.isEmpty_coe_sort]
--   · rintro A B hB hsu n
--     contrapose! hB
--     simp only [not_isEmpty_iff] at hB
--     obtain ⟨SubG⟩ := hB
--     simp only [acyclic, not_forall, not_isEmpty_iff]
--     use n
--     refine ⟨?_⟩
--     apply SubG.trans
--     apply (Es_spanningsubgraph_Es_of_subset _ hsu).toEmb
--   · rintro A B hAIndep hBIndep hAltB
--     have hA := (G.Es A).n_eq_m_add_c_of_acyclic hAIndep
--     have hB := (G.Es B).n_eq_m_add_c_of_acyclic hBIndep
--     rw [ncard_eq_card A, ncard_eq_card B] at hAltB
--     have hBNCltANC : (G.Es B).NumberOfComponents < (G.Es A).NumberOfComponents := by omega
--     clear hA hB hAltB
--     unfold NumberOfComponents at hBNCltANC
--     have : ¬ (G.Es B).connSetoid ≤ (G.Es A).connSetoid := by
--       apply not_imp_not.mpr (Quotient.card_quotient_le_card_quotient_of_ge)
--       convert hBNCltANC.not_le
--     simp only [Setoid.le_def, not_forall, Classical.not_imp] at this; clear hBNCltANC
--     obtain ⟨v, w, hvw, hvw'⟩ := this
--     simp only [connSetoid] at hvw hvw'
--     obtain ⟨n, S, hSstart, hSfinish⟩ := hvw.PathEmb
--     let i := Fin.find (fun x => ¬ (G.Es A).conn v (S.fᵥ x)) |>.get (Fin.isSome_find_iff.mpr
--       ⟨Fin.last n, by rwa [hSfinish]⟩)
--     have himem : i ∈ Fin.find (fun x => ¬ (G.Es A).conn v (S.fᵥ x)) := Option.get_mem _
--     have hspec : ¬ (G.Es A).conn v (S.fᵥ i) := by
--       apply Fin.find_spec (fun x => ¬ (G.Es A).conn v (S.fᵥ x)) himem
--     have hine0 : i ≠ 0 := by
--       intro h
--       rw [h, hSstart] at hspec
--       exact hspec (conn.refl _ _)
--     let iₑ := i.pred hine0
--     let ipred := iₑ.castSucc
--     have hipredconn : (G.Es A).conn v (S.fᵥ ipred) := by
--       have := Fin.find_min himem (Fin.castSucc_pred_lt hine0 : ipred < i)
--       simpa only [Decidable.not_not] using this
--     have : (PathGraph n).canGo ipred iₑ i = true := by
--       convert PathGraph.canGo' iₑ
--       exact (i.succ_pred hine0).symm
--     use S.fₑ iₑ, (S.fₑ iₑ).prop
--     constructor
--     · contrapose! hspec
--       apply Relation.ReflTransGen.tail hipredconn
--       use ⟨S.fₑ iₑ, hspec⟩
--       rw [← (Es_spanningsubgraph G A).canGo_iff, Es_spanningsubgraph_fᵥ, id_eq, id_eq,
--         Es_spanningsubgraph_fₑ]
--       exact (Es_spanningsubgraph G B).canGo <| S.canGo this
--     · simp
--       sorry
--   · rintro A hAIndep
--     simp only [Set.subset_univ]
--   done

-- -- #print axioms IndepMatroidOfFintype
