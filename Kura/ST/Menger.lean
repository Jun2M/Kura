import Kura.S-T.PathEnsemble
import Mathlib.Data.Set.Disjoint

namespace Graph
open Set Function List Nat Walk Path PathEnsemble
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w1 w2 : Walk α β}

namespace Graph

-- can be iff.
lemma IsEdgeSetSeparator.nonempty_inter (h : G.IsEdgeSetSeparator S T F)
    (hW : G.IsWalkFrom S T W) : ({e | e ∈ W.edge} ∩ F).Nonempty := sorry

lemma not_isVxSetSeparator_iff :
    ¬ G.IsVxSetSeparator X S T ↔ ∃ P, (G - X).IsPathFrom S T P := sorry

lemma foo1 (h : G.SetConnected S T) (hsep : G.IsEdgeSetSeparator S T F) :
    ∃ e x y, G.IsLink e x y ∧ e ∈ F ∧
      (G -ₑ {e}).SetConnected S {x} ∧ (G -ₑ {e}).SetConnected {y} T := sorry

-- lemma foo1 (G : Graph α β) (S T : Set α) (F : Set β) (hST : (G.edgeDel F).Connected S T) : sorry

open Path

set_option maxHeartbeats 1000000 in
theorem Menger_VxSet {α β : Type*} (G : Graph α β) [hfin : G.Finite] (S T : Set α)
    (k : ℕ)
    -- (hsep : ∀ U : Set α, U.Finite → G.IsVxSetSeparator U S T → k ≤ U.ncard)  :
    (hsep' : ∀ U, G.IsVxSetSeparator U S T → k ≤ U.encard) :
    ∃ (Ps : PathEnsemble α β), k ≤ Ps.Paths.encard ∧ Ps.ValidIn G ∧ Ps.StartSet ⊆ S ∧ Ps.FinishSet ⊆ T := by
  classical

  obtain hE | ⟨e, hE⟩ := E(G).eq_empty_or_nonempty
  · use PathEnsemble.nil (V(G) ∩ S ∩ T) β
    simp only [nil_encard, nil_validOn_iff, nil_firstSet, nil_lastSet, Set.inter_subset_right,
      and_true]
    refine ⟨hsep' _ ?_, by tauto_set⟩
    rintro a ha b hb hconn
    rw [connected_iff_eq_mem_of_E_empty] at hconn
    obtain ⟨rfl, haV, haX⟩ := hconn
    exact haX ⟨⟨haV, ha⟩, hb⟩
    · exact subset_eq_empty (induce_le G Set.diff_subset).2.1 hE


  by_cases h : ∀ U : Set α, G{E(G) \ {e}}.IsVxSetSeparator U S T → k ≤ U.encard
  · obtain ⟨Ps, hlen, hPVd, hPs⟩ := Menger_VxSet (G{E(G) \ {e}}) S T k h
    use Ps, hlen, hPVd.le (restrict_le _ _), hPs.1, hPs.2

  simp only [not_forall, Classical.not_imp, not_le] at h

  obtain ⟨U, hUsep, hUcard⟩ := h


  -- There is a path that uses e and none of the vertices in U
  have h : ¬ G.IsVxSetSeparator U S T :=  fun h ↦ hUcard.not_le <| hsep' U h
  obtain ⟨P, hP⟩ := not_isVxSetSeparator_iff.1 h
  have hsep'' : (G - U).IsEdgeSetSeparator S T {e} := by
    rw [IsEdgeSetSeparator]
    -- use commutativity of deletion
    sorry
  have heP : e ∈ P.edge := by simpa using hsep''.nonempty_inter hP.isWalkFrom

  -- simp only [IsVxSetSeparator, not_forall, Classical.not_imp, Decidable.not_not, exists_prop] at h
  -- obtain ⟨s, hs, t, ht, hconn⟩ := h
  -- obtain ⟨p, hpVdU, rfl, rfl⟩ := Connected.iff_path.mp hconn; clear hconn
  -- have hpe : e ∈ p.val.edge := by
  --   have hpVd : p.val.ValidIn G := hpVdU.le (induce_le G Set.diff_subset)
  --   by_contra! hpe
  --   refine hUsep p.val.first hs p.val.last ht
  --   <| p.val.connected_of_validOn
  --   <| hpVd.subgraph (fun _x hx ↦ hpVdU.mem_of_mem_vx hx)
  --   <| fun e' he' ↦ ⟨hpVd.mem_of_mem_edge he', ?_⟩
  --   simp only [mem_singleton_iff]
  --   rintro rfl
  --   exact hpe he'
  obtain ⟨w₁, w₂, hw12, hnin⟩ := Walk.eq_append_cons_of_edge_mem heP
  let x := w₁.last
  let y := w₂.first
  have hxy : G[V(G) \ U].IsLink e x y := (hw12 ▸ hpVdU).append_right_validOn.1
  have hxney : x ≠ y := ne_of_isLink_edge_mem hpVdU hxy hpe

  let Ge := (G - U){E(G) \ {e}}

  have hGeleGU : Ge ≤ G[V(G) \ U] := restrict_le _ _
  have hGxleGU : G - (U ∪ {x}) ≤ G - U := by
    rw [← vxDel_vxDel_eq_vxDel_union]
    exact vxDel_le (G - U)
  have hGyleGU : G - (U ∪ {y}) ≤ G - U := by
    rw [← vxDel_vxDel_eq_vxDel_union]
    exact vxDel_le (G - U)
  have hGeleG : Ge ≤ G := (restrict_le _ _).trans (vxDel_le _)
  -- Golf this somehow?
  have hGxleGe : (G - (U ∪ {x})) ≤ Ge := by
    rw [le_iff_of_mutual_le hGxleGU hGeleGU]
    use ?_, fun e ↦ ?_
    · rw [← vxDel_vxDel_eq_vxDel_union]
      simp only [vxDel_V, restrict_V, diff_singleton_subset_iff, Set.subset_insert, Ge, x]
    simp +contextual only [union_singleton, vxDel_E, mem_diff, Set.mem_insert_iff, not_or,
      Set.mem_inter_iff, mem_setOf_eq, restrict_E, not_false_eq_true, and_self, implies_true,
      mem_singleton_iff, true_and, and_imp, x, Ge]
    rintro he hinc rfl
    exact (hinc x (hxy.inc_left.le <| induce_le G Set.diff_subset)).2.1 rfl
  have hGyleGe : (G - (U ∪ {y})) ≤ Ge := by
    rw [le_iff_of_mutual_le hGyleGU hGeleGU]
    use ?_, fun e ↦ ?_
    · rw [← vxDel_vxDel_eq_vxDel_union]
      simp only [vxDel_V, restrict_V, diff_singleton_subset_iff, Set.subset_insert, Ge, x]
    simp +contextual only [union_singleton, vxDel_E, mem_diff, Set.mem_insert_iff, not_or,
      Set.mem_inter_iff, mem_setOf_eq, restrict_E, not_false_eq_true, and_self, implies_true,
      mem_singleton_iff, true_and, and_imp, Ge, x, y]
    rintro he hinc rfl
    exact (hinc y (hxy.inc_right.le <| induce_le G Set.diff_subset)).2.1 rfl

  have hUxconn : (G - (U ∪ {x})).Connected y p.val.last := by
    have hw₂last : w₂.last = p.val.last := by
      simp only [hw12, Walk.append_last, Walk.cons_last]
    refine hw₂last ▸ w₂.connected_of_validOn ?_
    obtain ⟨hbtw, h2VdU⟩ := (hw12 ▸ hpVdU).append_right_validOn
    have h2Vd := h2VdU.le (induce_le G Set.diff_subset)
    refine h2Vd.induce fun z hz2 ↦ ⟨h2Vd.mem_of_mem_vx hz2, ?_⟩
    simp only [union_singleton, Set.mem_insert_iff, (h2VdU.mem_of_mem_vx hz2).2, or_false, x]
    rintro rfl
    have := hw12 ▸ p.prop
    simp only [Walk.append_vx, Walk.cons_vx] at this
    exact List.not_nodup_cons_of_mem hz2 <| List.Nodup.of_append_right this
  have hUxFin : (U ∪ {x}).Finite := hUFin.union (finite_singleton x)
  have hUxSep : G.IsVxSetSeparator (U ∪ {x}) S T := by
    rintro a ha b hb hconn
    exact hUsep a ha b hb (hconn.le (vxDel_restrict_eq_restrict_vxDel _ _ ▸ hGxleGe))
  have hUxncard : (U ∪ {x}).ncard = k := by
    specialize hsep (U ∪ {x}) hUxFin hUxSep
    have : (U ∪ {x}).ncard ≤ U.ncard + 1 := by
      rw [union_singleton]
      exact ncard_insert_le x U
    omega
  have hxU : x ∉ U := by
    rintro hxU
    simp only [union_singleton, hxU, insert_eq_of_mem] at hUxncard
    omega
  have hUyconn : (G - (U ∪ {y})).Connected p.val.first x := by
    have hw₁first : w₁.first = p.val.first := by
      simp only [hw12, Walk.cons_first, Walk.append_first_of_eq]
    refine hw₁first ▸ w₁.connected_of_validOn ?_
    rw [hw12] at hpVdU
    by_cases h : w₁.Nonempty
    · have := hpVdU.append_left_validOn (by simp) h
      have h1Vd := this.le (induce_le G Set.diff_subset)
      refine Walk.ValidIn.induce h1Vd ?_
      rintro z hz2
      refine ⟨h1Vd.mem_of_mem_vx hz2, ?_⟩
      simp only [union_singleton, Set.mem_insert_iff, (this.mem_of_mem_vx hz2).2, or_false]
      rintro rfl
      have := p.prop
      rw [hw12] at this
      simp only [Walk.append_vx, Walk.cons_vx] at this
      rw [List.append_cons, Walk.last_eq_vx_getLast, List.dropLast_concat_getLast Walk.vx_ne_nil] at this
      exact List.disjoint_of_nodup_append this hz2 Walk.first_vx_mem
    · simp only [Walk.Nonempty.not_iff] at h
      obtain ⟨u, rfl⟩ := h
      simp only [Walk.nil_validOn_iff, induce_V, mem_diff]
      have : x = u := by
        unfold x
        rfl
      rw [this] at hxU hxney hxy
      refine ⟨diff_subset hxy.vx_mem_left, ?_⟩
      simp only [union_singleton, Set.mem_insert_iff, hxney, hxU, or_self, not_false_eq_true]
  have hUyFin : (U ∪ {y}).Finite := hUFin.union (finite_singleton y)
  have hUySep : G.IsVxSetSeparator (U ∪ {y}) S T := by
    rintro a ha b hb hconn
    exact hUsep a ha b hb (hconn.le (vxDel_restrict_eq_restrict_vxDel _ _ ▸ hGyleGe))
  have hUyncard : (U ∪ {y}).ncard = k := by
    specialize hsep (U ∪ {y}) hUyFin hUySep
    have : (U ∪ {y}).ncard ≤ U.ncard + 1 := by
      rw [union_singleton]
      exact ncard_insert_le y U
    omega
  have hyU : y ∉ U := by
    rintro hyU
    simp only [union_singleton, hyU, insert_eq_of_mem] at hUyncard
    omega
  have hUV : U ⊆ V(G) := by
    change ∀ x ∈ U, x ∈ V(G)
    by_contra! hUV
    obtain ⟨u, huU, huv⟩ := hUV
    have hUdiffu : ((U ∪ {x}) \ {u}).ncard < (U ∪ {x}).ncard := by
      refine Set.ncard_lt_ncard ?_ hUxFin
      simp only [union_singleton, diff_singleton_sSubset, Set.mem_insert_iff, huU, or_true, Ge, x]
    specialize hsep ((U ∪ {x}) \ {u}) (Finite.diff hUxFin) ?_
    · rintro a ha b hb hconn
      refine hUxSep a ha b hb ?_
      convert hconn using 1
      rw [vxDel_eq_vxDel_iff, Set.diff_diff_right, eq_comm, Set.union_eq_left,
        Set.inter_singleton_eq_empty.mpr huv]
      exact empty_subset (V(G) \ (U ∪ {x}))
    omega
  have hUx : (U ∪ {x}) ⊆ V(G) := by
    simp [hUV, Set.insert_subset_iff, (Set.diff_subset hxy.vx_mem_left)]
  have hUy : (U ∪ {y}) ⊆ V(G) := by
    simp [hUV, Set.insert_subset_iff, (Set.diff_subset hxy.vx_mem_right)]

  let L : Set α := hUxSep.leftSet
  let R : Set α := hUySep.rightSet
  have hLy : y ∉ L := by
    rintro ⟨s, hs, hconn⟩
    exact hUxSep s hs p.val.last ht <| hconn.symm.trans hUxconn
  have hRx : x ∉ R := by
    rintro ⟨t, ht, hconn⟩
    exact hUySep p.val.first hs t ht <| hUyconn.trans hconn

  have hLV : L ⊆ V(G) := by
    rintro l ⟨s, hs, hconn⟩
    exact diff_subset hconn.mem_left
  obtain ⟨Psx, hlenx, hPVdx, hPsxStartSet, hPsxFinishSet⟩ :=
    Menger_VxSet (hfin := ⟨(hfin.vx_fin.subset hLV).union hUxFin, hfin.edge_fin.subset (induce_E_le (L ∪ (U ∪ {x})))⟩)
      (G[L ∪ (U ∪ {x})]) S (U ∪ {x}) k (fun V hVFin hVsep ↦
      hsep V hVFin (IsVxSetSeparator.IsPreorder.trans V (U ∪ {x}) T ((hUxSep.leftSetV_iff hUx _).mp hVsep) hUxSep))
  have hRV : R ⊆ V(G) := by
    rintro r ⟨t, ht, hconn⟩
    exact Set.diff_subset hconn.mem_left
  obtain ⟨Psy, hleny, hPVdy, hPsyStartSet, hPsyFinishSet⟩ :=
    Menger_VxSet (hfin := ⟨(hfin.vx_fin.subset hRV).union hUyFin, hfin.edge_fin.subset (induce_E_le (R ∪ (U ∪ {y})))⟩)
      (G[R ∪ (U ∪ {y})]) (U ∪ {y}) T k (fun V hVFin hVsep ↦
      hsep V hVFin (IsVxSetSeparator.IsPreorder.trans V (U ∪ {y}) S ((hUySep.symm.leftSetV_iff hUy _).mp hVsep.symm) hUySep.symm).symm)

  let PU : PathEnsemble α β := PathEnsemble.insert (hxy.path hxney) (PathEnsemble.nil U β) (by
    rintro z hz
    simp only [hxy.path_vx, mem_cons, notMem_nil, or_false] at hz
    obtain rfl | rfl := hz <;> simp only [PathEnsemble.nil_VxSet, hxU, hyU, not_false_eq_true])

  have hPUVdUxy : PU.ValidIn (G[insert x (insert y U)]) := by
    rintro p (hp | rfl)
    · refine (PathEnsemble.nil_validOn p hp).le (induce_le_induce (le_refl _) ?_)
      exact (Set.subset_insert _ _).trans (subset_insert _ _)
    · refine IsLink.path_validOn ?_ hxney
      simp only [induce_isLink_iff, hxy.le (induce_le _ diff_subset), Set.mem_insert_iff,
        true_or, or_true, and_self, x]

  /- Now that I have two set of path ensembles, each corresponding to a unique element in
  Ux/Uy, I can append them to get a path ensemble for G. -/
  have hPsxFinishSet : Psx.FinishSet = U ∪ {x} := by
    apply Set.eq_of_subset_of_ncard_le hPsxFinishSet ?_ hUxFin
    rw [hUxncard, PathEnsemble.FinishSet_ncard, hlenx]
  have hPUStartSet : PU.StartSet = U ∪ {x} := by
    simp only [PathEnsemble.insert_firstSet, PathEnsemble.nil_firstSet, union_singleton, PU]
    congr
  have hPUFinishSet : PU.FinishSet = U ∪ {y} := by
    simp only [PathEnsemble.insert_lastSet, PathEnsemble.nil_lastSet, union_singleton, PU]
    congr
  have hPsyStartSet : Psy.StartSet = U ∪ {y} := by
    apply Set.eq_of_subset_of_ncard_le hPsyStartSet ?_ hUyFin
    rw [hUyncard, PathEnsemble.StartSet_ncard, hleny]
  have hsu1 : Psx.VxSet ∩ PU.VxSet ⊆ Psx.FinishSet := by
    rw [hPsxFinishSet]
    refine (Set.inter_subset_inter (PathEnsemble.VxSet_subset_of_validOn hPVdx) (PathEnsemble.VxSet_subset_of_validOn hPUVdUxy)).trans ?_
    suffices (L ∪ (U ∪ {x})) ∩ ({y} ∪ (U ∪ {x})) ⊆ U ∪ {x} by
      convert this using 2
      simp only [induce_V, union_singleton, union_insert, singleton_union]
    rw [← Set.inter_union_distrib_right]
    simp only [union_subset_iff, subset_refl, and_true]
    rw [inter_singleton_eq_empty.mpr hLy]
    exact empty_subset (U ∪ {x})
  have heq1 : Psx.FinishSet = PU.StartSet := hPsxFinishSet.trans hPUStartSet.symm
  have hsu2 : (Psx.append PU hsu1 heq1).VxSet ∩ Psy.VxSet ⊆ (Psx.append PU hsu1 heq1).FinishSet := by

    sorry
  have heq2 : (Psx.append PU hsu1 heq1).FinishSet = Psy.StartSet := by
    sorry

  let P := (Psx.append PU hsu1 heq1).append Psy hsu2 heq2
  use P, ?_, ?_, ?_
  · rwa [append_lastSet]
  · rwa [append_ncard_eq_right, ← StartSet_ncard, hPsyStartSet]
  · apply PathEnsemble.append_validOn
    · apply PathEnsemble.append_validOn (hPVdx.le (induce_le G <| union_subset hLV hUx))
      refine (hPUVdUxy.le (induce_le G ?_))
      refine insert_subset hxy.vx_mem_left.1 (insert_subset hxy.vx_mem_right.1 hUV)
    · exact hPVdy.le (induce_le G <| union_subset hRV hUy)
  · rwa [append_firstSet, append_firstSet]
termination_by E(G).ncard
decreasing_by
  · refine lt_of_le_of_lt (Set.ncard_inter_le_ncard_right E(G) _ hfin.edge_fin.diff) ?_
    rw [Set.ncard_diff (by simp only [singleton_subset_iff, he])]
    simp only [ncard_singleton, tsub_lt_self_iff, lt_one_iff, pos_of_gt, and_true]
    rw [Set.ncard_pos hfin.edge_fin]
    exact nonempty_of_mem he
  · refine ncard_lt_ncard ?_ hfin.edge_fin
    have hle : G[hUxSep.leftSet ∪ (U ∪ {w₁.last})] ≤ G := induce_le G <| union_subset hLV hUx
    refine ssubset_of_subset_not_subset hle.2.1 ?_
    · rw [not_subset_iff_exists_mem_notMem]
      use e, he
      intro he'
      have hinc := hxy.inc_right.le (induce_le G diff_subset)
      rw [← Inc_iff_Inc_of_le hle he'] at hinc
      have := hinc.vx_mem
      unfold L at hLy
      unfold x at hxney
      simp [hLy, hyU, hxney.symm] at this
  · refine ncard_lt_ncard ?_ hfin.edge_fin
    have hle : G[hUySep.rightSet ∪ (U ∪ {w₂.first})] ≤ G := induce_le G <| union_subset hRV hUy
    refine ssubset_of_subset_not_subset hle.2.1 ?_
    · rw [not_subset_iff_exists_mem_notMem]
      use e, he
      intro he'
      have hinc := hxy.inc_left.le (induce_le G diff_subset)
      rw [← Inc_iff_Inc_of_le hle he'] at hinc
      have := hinc.vx_mem
      unfold R at hRx
      unfold y at hxney
      simp [hRx, hxU, hxney] at this
