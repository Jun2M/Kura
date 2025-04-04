import Kura.Walk

open Set Function List Nat
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β}

namespace Graph
namespace Path

set_option maxHeartbeats 1000000 in
theorem Menger_VxSet {α β : Type*} [DecidableEq α] (G : Graph α β) [hfin : G.Finite] (S T : Set α) (k : ℕ)
    (hS : S.Finite) (hT : T.Finite)
    (hsep : ∀ U : Set α, U.Finite → G.IsVxSetSeparator U S T → k ≤ U.ncard) :
    ∃ Ps : PathEnsemble α β, (Ps.Paths.ncard = k) ∧ Ps.ValidOn G ∧ Ps.StartSet ⊆ S ∧ Ps.FinishSet ⊆ T := by
  classical
  by_cases hE : G.E.Nonempty
  · obtain ⟨e, he⟩ := hE
    let G' := G{G.E \ {e}}
    have hG'le : G{G.E \ {e}} ≤ G := restrict_le G _
    by_cases h : ∀ U : Set α, U.Finite → G{G.E \ {e}}.IsVxSetSeparator U S T → k ≤ U.ncard
    · -- Deleting the edge did not decrease k, so get the paths from the smaller graph
      have hG'term : (G.E ∩ (G.E \ {e})).ncard + k < G.E.ncard + k := by
        simp only [restrict_E, add_lt_add_iff_right]
        apply Set.ncard_lt_ncard ?_ Finite.edge_fin
        refine inter_ssubset_left_iff.mpr ?_
        rintro hsu
        have := hsu he
        simp at this
      have := Menger_VxSet (G{G.E \ {e}}) S T k hS hT h
      obtain ⟨Ps, hlen, hPVd, hPs⟩ := this
      use Ps, hlen, fun p hp ↦ (hPVd p hp).le hG'le
    · simp only [not_forall, Classical.not_imp, not_le] at h
      obtain ⟨U, hUFin, hUsep, hUcard⟩ := h

      -- There is a path that uses e and none of the vertices in U
      have : ¬ G.IsVxSetSeparator U S T := by
        rintro h
        specialize hsep U hUFin h
        omega
      simp only [IsVxSetSeparator, not_forall, Classical.not_imp, Decidable.not_not] at this
      obtain ⟨s, hs, t, ht, hconn⟩ := this
      rw [Connected.iff_path] at hconn
      obtain ⟨p, hpVdU, rfl, rfl⟩ := hconn
      have hpVd : p.ValidOn G := hpVdU.le (induce_le G Set.diff_subset)
      have hpe : e ∈ p.edge := by
        by_contra! hpe
        apply hUsep p.start hs p.finish ht
        rw [restrict_V]
        apply p.val.connected_of_validOn
        apply hpVd.subgraph
        · rintro x hx
          exact hpVdU.mem_of_mem_vx hx
        · rintro e' he'
          refine ⟨hpVd.mem_of_mem_edge he', ?_⟩
          simp only [mem_singleton_iff]
          rintro rfl
          exact hpe he'
      obtain ⟨w₁, w₂, hw12, hnin⟩ := Walk.eq_append_cons_of_edge_mem hpe
      have hw₁start : w₁.start = p.start := by
        unfold Path.start
        rw [hw12]
        simp only [Walk.cons_start, Walk.append_start_of_eq]
      have hw₂finish : w₂.finish = p.finish := by
        unfold Path.finish
        rw [hw12]
        simp only [Walk.append_finish, Walk.cons_finish]
      let x := w₁.finish
      let y := w₂.start
      have hxy : G[G.V \ U].IsBetween e x y := by
        simp only [ValidOn, hw12] at hpVdU
        obtain ⟨hbtw, H2⟩ := hpVdU.append_right_validOn
        exact hbtw
      have hxney : x ≠ y := by
        rintro hxeqy
        rw [hxeqy] at hxy
        have hloop : G[G.V \ U].IsLoop e := by
          rw [IsLoop_iff_IsBetween]
          use y
        exact edge_not_isLoop hpe hpVdU hloop

      let Ux := U ∪ {x}
      have hUxconn : G[G.V \ Ux].Connected y p.finish := by
        rw [← hw₂finish]
        refine w₂.connected_of_validOn ?_
        unfold Path.ValidOn at hpVdU
        rw [hw12] at hpVdU
        have := hpVdU.append_right_validOn
        rw [Walk.cons_validOn_iff] at this
        have h2Vd := this.2.le (induce_le G Set.diff_subset)
        refine Walk.ValidOn.induce h2Vd ?_
        rintro z hz2
        refine ⟨h2Vd.mem_of_mem_vx hz2, ?_⟩
        simp only [union_singleton, Set.mem_insert_iff, (this.2.mem_of_mem_vx hz2).2, or_false, Ux]
        rintro rfl
        have := p.prop
        rw [hw12] at this
        simp only [Walk.append_vx, Walk.cons_vx] at this
        exact List.not_nodup_cons_of_mem hz2 <| List.Nodup.of_append_right this
      have hUxFin : Ux.Finite := hUFin.union (finite_singleton x)
      have hUxSep : G.IsVxSetSeparator Ux S T := by
        rintro a ha b hb hconn
        refine hUsep a ha b hb (hconn.le ?_)
        simp only [restrict_V]
        rw [le_of_exist_mutual_le]
        refine ⟨?_, ?_⟩
        · simp only [union_singleton, induce_V, Ux]
          rw [Set.diff_subset_comm]
          simp only [sdiff_sdiff_right_self, inf_eq_inter]
          exact Set.inter_subset_right.trans (Set.subset_insert x U)
        · rintro f
          simp +contextual only [union_singleton, induce_E, mem_diff, Set.mem_insert_iff, not_or,
            Set.mem_inter_iff, mem_setOf_eq, restrict_E, restrict_inc, mem_singleton_iff, and_imp,
            true_and, not_false_eq_true, and_self, implies_true, imp_self, and_true, Ux, x]
          rintro hf hf' rfl
          specialize hf' x (hxy.le (induce_le G Set.diff_subset)).inc_left
          simp only [not_true_eq_false, false_and, and_false, x, Ux] at hf'
        · exact induce_le G Set.diff_subset
        · exact (induce_le _ Set.diff_subset).trans (restrict_le G _)
      have hUxncard : Ux.ncard = k := by
        specialize hsep Ux hUxFin hUxSep
        have : Ux.ncard ≤ U.ncard + 1 := by
          simp only [union_singleton, Ux]
          exact ncard_insert_le x U
        omega
      have hxU : x ∉ U := by
        rintro hxU
        simp only [union_singleton, hxU, insert_eq_of_mem, Ux] at hUxncard
        omega
      let Uy := U ∪ {y}
      have hUyconn : G[G.V \ Uy].Connected p.start x := by
        rw [← hw₁start]
        refine w₁.connected_of_validOn ?_
        unfold Path.ValidOn at hpVdU
        rw [hw12] at hpVdU
        by_cases h : w₁.Nonempty
        · have := hpVdU.append_left_validOn (by simp) h
          have h1Vd := this.le (induce_le G Set.diff_subset)
          refine Walk.ValidOn.induce h1Vd ?_
          rintro z hz2
          refine ⟨h1Vd.mem_of_mem_vx hz2, ?_⟩
          simp only [union_singleton, Set.mem_insert_iff, (this.mem_of_mem_vx hz2).2, or_false, Uy]
          rintro rfl
          have := p.prop
          rw [hw12] at this
          simp only [Walk.append_vx, Walk.cons_vx] at this
          rw [List.append_cons, Walk.finish_eq_vx_getLast, List.dropLast_concat_getLast Walk.vx_ne_nil] at this
          exact List.disjoint_of_nodup_append this hz2 Walk.start_vx_mem
        · simp only [Walk.Nonempty.not_iff, Uy] at h
          obtain ⟨u, rfl⟩ := h
          simp only [Walk.nil_validOn_iff, induce_V, mem_diff, Uy]
          have : x = u := by
            unfold x
            rfl
          rw [this] at hxU hxney hxy
          refine ⟨diff_subset hxy.vx_mem_left, ?_⟩
          simp only [union_singleton, Set.mem_insert_iff, hxney, hxU, or_self, not_false_eq_true]

      have hUyFin : Uy.Finite := hUFin.union (finite_singleton y)
      have hUySep : G.IsVxSetSeparator Uy S T := by
        rintro a ha b hb hconn
        refine hUsep a ha b hb (hconn.le ?_)
        simp only [restrict_V]
        rw [le_of_exist_mutual_le]
        refine ⟨?_, ?_⟩
        · simp only [union_singleton, induce_V, Uy]
          rw [Set.diff_subset_comm]
          simp only [sdiff_sdiff_right_self, inf_eq_inter]
          exact Set.inter_subset_right.trans (Set.subset_insert y U)
        · rintro f
          simp +contextual only [union_singleton, induce_E, mem_diff, Set.mem_insert_iff, not_or,
            Set.mem_inter_iff, mem_setOf_eq, restrict_E, restrict_inc, mem_singleton_iff, and_imp,
            true_and, not_false_eq_true, and_self, implies_true, imp_self, and_true, Uy, y]
          rintro hf hf' rfl
          specialize hf' y (hxy.le (induce_le G Set.diff_subset)).inc_right
          simp only [not_true_eq_false, false_and, and_false, y, Uy] at hf'
        · exact induce_le G Set.diff_subset
        · exact (induce_le _ Set.diff_subset).trans (restrict_le G _)
      have hUyncard : Uy.ncard = k := by
        specialize hsep Uy hUyFin hUySep
        have : Uy.ncard ≤ U.ncard + 1 := by
          simp only [union_singleton, Uy]
          exact ncard_insert_le y U
        omega
      have hyU : y ∉ U := by
        rintro hyU
        simp only [union_singleton, hyU, insert_eq_of_mem, Uy] at hUyncard
        omega
      have hUV : U ⊆ G.V := by
        change ∀ x ∈ U, x ∈ G.V
        by_contra! hUV
        obtain ⟨u, huU, huv⟩ := hUV
        have hUdiffu : (Ux \ {u}).ncard < Ux.ncard := by
          refine Set.ncard_lt_ncard ?_ hUxFin
          simp only [union_singleton, diff_ssubset_left_iff, inter_singleton_nonempty,
            Set.mem_insert_iff, huU, or_true, Ux, x, Uy, y]
        specialize hsep (Ux \ {u}) (Finite.diff hUxFin) ?_
        · rintro a ha b hb hconn
          refine hUxSep a ha b hb ?_
          convert hconn using 2
          rw [Set.diff_diff_right, eq_comm, Set.union_eq_left, Set.inter_singleton_eq_empty.mpr huv]
          exact empty_subset (G.V \ Ux)
        omega
      have hUx : Ux ⊆ G.V := by
        simp [Ux, hUV, Set.insert_subset_iff, (Set.diff_subset hxy.vx_mem_left)]
      have hUy : Uy ⊆ G.V := by
        simp [Uy, hUV, Set.insert_subset_iff, (Set.diff_subset hxy.vx_mem_right)]

      let PU : PathEnsemble α β := PathEnsemble.insert (hxy.path hxney) (PathEnsemble.nil U β) (by
        rintro z hz
        simp only [hxy.path_vx, mem_cons, not_mem_nil, or_false] at hz
        obtain rfl | rfl := hz <;> simp only [PathEnsemble.nil_VxSet, hxU, hyU, not_false_eq_true])
      have hxyVdG : (hxy.path hxney).ValidOn G := hxy.walk_validOn.le (induce_le G Set.diff_subset)
      have hPUVdUxy : PU.ValidOn (G[insert x (insert y U)]) := by
        rintro p (hp | hp)
        · simp only [PathEnsemble.mem_nil_iff, nil] at hp
          obtain ⟨u, hu, rfl⟩ := hp
          simp only [ValidOn, Walk.nil_validOn_iff, induce_V, Set.mem_insert_iff, hu, or_true]
        · rw [mem_singleton_iff] at hp
          subst p
          simp only [ValidOn]
          refine Walk.ValidOn.induce hxyVdG ?_
          rintro a ha
          simp only [IsBetween.path, IsBetween.Walk.vx, mem_cons, not_mem_nil, or_false] at ha
          obtain rfl | rfl := ha <;> simp

      let L : Set α := hUxSep.leftSet
      let R : Set α := hUySep.rightSet
      have hLy : y ∉ L := by
        rintro ⟨s, hs, hconn⟩
        exact hUxSep s hs p.finish ht <| hconn.symm.trans hUxconn
      have hRx : x ∉ R := by
        rintro ⟨t, ht, hconn⟩
        exact hUySep p.start hs t ht <| hUyconn.trans hconn

      have hLV : L ⊆ G.V := by
        rintro l ⟨s, hs, hconn⟩
        exact Set.diff_subset hconn.mem_left
      have hSUxSepCard : ∀ (U : Set α), U.Finite → G[L ∪ Ux].IsVxSetSeparator U S Ux → k ≤ U.ncard := by
        rintro V hVFin hVsep
        refine hsep V hVFin (IsVxSetSeparator.IsPreorder.trans V Ux T ?_ hUxSep)
        rw [← hUxSep.leftSetV_iff hUx]
        exact hVsep
      have hFin : G[L ∪ Ux].Finite := by
        refine ⟨?_, ?_⟩
        · apply Set.Finite.union (Set.Finite.subset hfin.vx_fin ?_) hUxFin
          rintro x hx
          obtain ⟨s, hs, hconn⟩ := hx
          exact Set.diff_subset hconn.mem_left
        · exact Set.Finite.subset hfin.edge_fin (induce_E_le (L ∪ Ux))
      have := Menger_VxSet (hfin := hFin) (G[L ∪ Ux]) S Ux k hS hUxFin hSUxSepCard
      obtain ⟨Psx, hlenx, hPVdx, hPsxStartSet, hPsxFinishSet⟩ := this


      have hRV : R ⊆ G.V := by
        rintro r ⟨t, ht, hconn⟩
        exact Set.diff_subset hconn.mem_left
      have hSUySepCard : ∀ (U : Set α), U.Finite → G[R ∪ Uy].IsVxSetSeparator U Uy T → k ≤ U.ncard := by
        rintro V hVFin hVsep
        rw [IsVxSetSeparator.comm] at hVsep hUySep
        refine hsep V hVFin (IsVxSetSeparator.IsPreorder.trans V Uy S ?_ hUySep).symm
        rw [← hUySep.leftSetV_iff hUy]
        exact hVsep
      have hFin : G[R ∪ Uy].Finite := by
        refine ⟨?_, ?_⟩
        · apply Set.Finite.union (Set.Finite.subset hfin.vx_fin ?_) hUyFin
          rintro x hx
          obtain ⟨s, hs, hconn⟩ := hx
          exact Set.diff_subset hconn.mem_left
        · exact Set.Finite.subset hfin.edge_fin (induce_E_le (R ∪ Uy))
      have := Menger_VxSet (hfin := hFin) (G[R ∪ Uy]) Uy T k hUyFin hT hSUySepCard
      obtain ⟨Psy, hleny, hPVdy, hPsyStartSet, hPsyFinishSet⟩ := this

      /- TODO: Now that I have two set of path ensembles, each corresponding to a unique element in
      Ux/Uy, I can append them to get a path ensemble for G. -/
      have hPsxFinishSet : Psx.FinishSet = Ux := by
        apply Set.eq_of_subset_of_ncard_le hPsxFinishSet ?_ hUxFin
        · rw [hUxncard, PathEnsemble.FinishSet_ncard, hlenx]
      have hPUStartSet : PU.StartSet = Ux := by
        simp only [PathEnsemble.insert_startSet, PathEnsemble.nil_startSet, start, union_singleton,
          PU, Ux]
        congr
      have hPUFinishSet : PU.FinishSet = Uy := by
        simp only [PathEnsemble.insert_finishSet, PathEnsemble.nil_finishSet, finish,
          union_singleton, PU, Uy]
        congr
      have hPsyStartSet : Psy.StartSet = Uy := by
        apply Set.eq_of_subset_of_ncard_le hPsyStartSet ?_ hUyFin
        · rw [hUyncard, PathEnsemble.StartSet_ncard, hleny]
      have hPsxFin : Psx.Paths.Finite := Set.finite_of_ncard_pos (by omega)
      have hPUFin : PU.Paths.Finite := by
        apply PathEnsemble.finite_of_finite_graph ?_ hPUVdUxy
        apply finite_of_finite_induce
        apply Set.Finite.insert
        apply Set.Finite.insert _ hUFin
      have hPsyFin : Psy.Paths.Finite := Set.finite_of_ncard_pos (by omega)
      have hPsxPU : Psx.VxSet ∩ PU.VxSet = Psx.FinishSet := by
        apply subset_antisymm
        · rw [hPsxFinishSet]
          refine (Set.inter_subset_inter (PathEnsemble.VxSet_subset_of_validOn hPVdx) (PathEnsemble.VxSet_subset_of_validOn hPUVdUxy)).trans ?_
          simp only [induce_V, Uy]
          suffices (L ∪ Ux) ∩ ({y} ∪ Ux) ⊆ Ux by
            convert this using 2
            simp [Ux]
          rw [← Set.inter_union_distrib_right]
          simp only [union_subset_iff, subset_refl, and_true]
          have : L ∩ {y} = ∅ := inter_singleton_eq_empty.mpr hLy
          rw [this]
          exact empty_subset Ux
        · rw [subset_inter_iff]
          use Psx.finishSet_subset_VxSet
          rw [hPsxFinishSet]
          convert PU.startSet_subset_VxSet
          exact hPUStartSet.symm
      have hPUPsx : Psx.VxSet ∩ PU.VxSet = PU.StartSet := by
        rwa [hPUStartSet, ← hPsxFinishSet]
      have hPUPsy : (Psx.append PU hPsxPU hPUPsx).VxSet ∩ Psy.VxSet =
        (Psx.append PU hPsxPU hPUPsx).FinishSet := by

        sorry
      have hPsyPU : (Psx.append PU hPsxPU hPUPsx).VxSet ∩ Psy.VxSet = Psy.StartSet := by
        sorry
      let P := (Psx.append PU hPsxPU hPUPsx).append Psy hPUPsy hPsyPU
      use P, ?_, ?_, ?_
      · rwa [PathEnsemble.append_finishSet]
      · rw [PathEnsemble.append_ncard_eq_right, ← PathEnsemble.StartSet_ncard, hPsyStartSet]
        exact hUyncard
        exact hPsyFin
      · apply PathEnsemble.append_validOn
        · apply PathEnsemble.append_validOn
          · refine hPVdx.le (induce_le G ?_)
            rintro a (ha | ha)
            · exact hLV ha
            · exact hUx ha
          · refine (hPUVdUxy.le (induce_le G ?_))
            rintro a (rfl | rfl | ha)
            · refine hUx (?_ : x ∈ Ux)
              simp [Ux]
            · refine hUy (?_ : y ∈ Uy)
              simp [Uy]
            · exact hUV ha
        · refine hPVdy.le (induce_le G ?_)
          rintro a (ha | ha)
          · exact hRV ha
          · exact hUy ha
      · rw [PathEnsemble.append_startSet, PathEnsemble.append_startSet]
        exact hPsxStartSet

  · rw [Set.nonempty_iff_ne_empty, not_not] at hE
    let X := G.V ∩ S ∩ T
    have hXfin : X.Finite := Finite.inter_of_right hT (G.V ∩ S)
    have hXsep : G.IsVxSetSeparator X S T := by
      rintro a ha b hb hconn
      rw [connected_iff_eq_mem_of_E_empty] at hconn
      obtain ⟨rfl, haV, haX⟩ := hconn
      exact haX ⟨⟨haV, ha⟩, hb⟩
      · exact subset_eq_empty (induce_le G Set.diff_subset).2.1 hE
    have hk : k ≤ X.ncard := hsep X hXfin hXsep
    obtain ⟨Y, hYsu, hYcard⟩ := exists_subset_card_eq hk
    use PathEnsemble.nil Y β, hYcard ▸ PathEnsemble.nil_ncard, PathEnsemble.nil_validOn ?_, ?_, ?_
    · exact hYsu.trans <| Set.inter_subset_left.trans Set.inter_subset_left
    · rw [PathEnsemble.nil_startSet]
      exact hYsu.trans (Set.inter_subset_left.trans Set.inter_subset_right)
    · rw [PathEnsemble.nil_finishSet]
      exact hYsu.trans Set.inter_subset_right
termination_by G.E.ncard
decreasing_by
  · refine lt_of_le_of_lt (Set.ncard_inter_le_ncard_right G.E _ hfin.edge_fin.diff) ?_
    rw [Set.ncard_diff (by simp only [singleton_subset_iff, he])]
    simp only [ncard_singleton, tsub_lt_self_iff, lt_one_iff, pos_of_gt, and_true]
    rw [Set.ncard_pos hfin.edge_fin]
    exact nonempty_of_mem he
  · refine ncard_lt_ncard ?_ hfin.edge_fin
    have hle : G[hUxSep.leftSet ∪ (U ∪ {w₁.finish})] ≤ G := induce_le G <| union_subset hLV hUx
    refine ssubset_of_subset_not_subset hle.2.1 ?_
    · rw [not_subset_iff_exists_mem_not_mem]
      use e, he
      intro he'
      have hinc := hxy.inc_right.le (induce_le G diff_subset)
      rw [← hle.2.2 _ _ he'] at hinc
      have := hinc.vx_mem
      unfold L at hLy
      unfold x at hxney
      simp [hLy, hyU, hxney.symm] at this
  · refine ncard_lt_ncard ?_ hfin.edge_fin
    have hle : G[hUySep.rightSet ∪ (U ∪ {w₂.start})] ≤ G := induce_le G <| union_subset hRV hUy
    refine ssubset_of_subset_not_subset hle.2.1 ?_
    · rw [not_subset_iff_exists_mem_not_mem]
      use e, he
      intro he'
      have hinc := hxy.inc_left.le (induce_le G diff_subset)
      rw [← hle.2.2 _ _ he'] at hinc
      have := hinc.vx_mem
      unfold R at hRx
      unfold y at hxney
      simp [hRx, hxU, hxney] at this
