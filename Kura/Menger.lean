import Kura.Walk2

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
      have hUcard' : U.ncard = k -1 := by sorry -- TODO: deal with k = 0 case
      have hUV : U ⊆ G.V := by sorry

      -- There is a path that uses e and none of the vertices in U
      -- TODO: Just use Connected.exists_walk?
      have hterm : (G.E ∩ {e | ∀ (x : α), G.Inc x e → x ∈ G.V ∧ x ∉ U}).ncard + 1 < G.E.ncard + k := by
        have : (G.E ∩ {e | ∀ (x : α), G.Inc x e → x ∈ G.V ∧ x ∉ U}).ncard ≤ G.E.ncard :=
          Set.ncard_inter_le_ncard_left G.E _ hfin.edge_fin
        suffices 1 < k by
          omega
        sorry -- TODO: deal with k = 1 case too
      obtain ⟨Ps, hlen, hPVd, hPsStart, hPsFinish⟩ := Menger_VxSet (hfin := finite_of_finite_induce hfin.vx_fin.diff)
        (G[G.V \ U]) S T 1 hS hT (by
        rintro V hVFin hVsep
        by_contra! hVcard
        simp only [lt_one_iff, hVFin, ncard_eq_zero] at hVcard
        subst V
        simp only [IsVxSetSeparator, induce_V, diff_empty, induce_idem] at hVsep
        have := hsep U hUFin hVsep
        omega)
      simp only [ncard_eq_one] at hlen
      obtain ⟨p, hp⟩ := hlen
      simp only [PathEnsemble.ValidOn, hp, mem_singleton_iff, forall_eq] at hPVd
      have hpmem : p ∈ Ps.Paths := by simp only [hp, mem_singleton_iff]
      have hpe : e ∈ p.edge := by
        by_contra! hpe
        refine hUsep p.start (hPsStart (Ps.start_mem_StartSet hpmem)) p.finish
          (hPsFinish (Ps.finish_mem_FinishSet hpmem)) (Walk.connected_of_validOn ?_)
        have := Walk.ValidOn.restrict hPVd (?_ : ∀ f ∈ p.edge, f ∈ G.E \ {e})
        simpa only [restrict_V, induce_restrict_eq_subgraph] using this
        · rintro f hf
          refine ⟨Set.mem_of_mem_inter_left (Walk.ValidOn.mem_of_mem_edge hPVd hf), ?_⟩
          rw [mem_singleton_iff]
          rintro rfl
          exact hpe hf

      obtain ⟨w₁, w₂, hw12, hnin⟩ := Walk.eq_append_cons_of_edge_mem hpe
      let x := w₁.finish
      let y := w₂.start
      have hxy : G[G.V \ U].IsBetween e x y := by
        simp only [ValidOn, hw12] at hPVd
        obtain ⟨hbtw, H2⟩ := hPVd.append_right_validOn
        exact hbtw
      have hxney : x ≠ y := by
        rintro hxeqy
        rw [hxeqy] at hxy
        have hloop : G[G.V \ U].IsLoop e := by
          rw [IsLoop_iff_IsBetween]
          use y
        exact edge_not_isLoop hpe hPVd hloop

      /- TODO: U is a separator on G - e. If U contains either x or y, then removing U from G also removes
      the edge e. This implies that U is also a separator of G. As U is smaller than k, this is a
      contradiction. -/
      have hxU : x ∉ U := by sorry
      have hyU : y ∉ U := by sorry

      let PU : PathEnsemble α β := {
        Paths := insert (IsBetween.path hxy hxney) (Path.nil '' U)
        Disj := by
          rintro z p q hp hq hzp hzq
          simp only [Set.mem_insert_iff, mem_image] at hp hq
          obtain rfl | ⟨z', hz', rfl⟩ := hp <;> obtain rfl | ⟨z'', hz'', rfl⟩ := hq
          · rfl
          · simp only [vx, nil, Walk.nil_vx, mem_cons, not_mem_nil, or_false, IsBetween.path,
            IsBetween.Walk.vx] at hzq hzp
            subst z''
            obtain rfl | rfl := hzp
            · exact False.elim (hxU hz'')
            · exact False.elim (hyU hz'')
          · simp only [vx, nil, Walk.nil_vx, mem_cons, not_mem_nil, or_false, IsBetween.path,
            IsBetween.Walk.vx] at hzq hzp
            subst z'
            obtain rfl | rfl := hzq
            · exact False.elim (hxU hz')
            · exact False.elim (hyU hz')
          · simp only [vx, nil, Walk.nil_vx, mem_cons, not_mem_nil, or_false] at hzp hzq
            subst z' z''
            rfl
      }

      have hterm : (G.E ∩ (G.E \ {e})).ncard < G.E.ncard := by
        refine lt_of_le_of_lt (Set.ncard_inter_le_ncard_right G.E _ hfin.edge_fin.diff) ?_
        rw [Set.ncard_diff (by simp only [singleton_subset_iff, he])]
        simp only [ncard_singleton, tsub_lt_self_iff, lt_one_iff, pos_of_gt, and_true]
        rw [Set.ncard_pos hfin.edge_fin]
        exact nonempty_of_mem he

      let Ux := U ∪ {x}
      have hUx : Ux ⊆ G.V := by
        simp [Ux, hUV, Set.insert_subset_iff, (Set.diff_subset hxy.vx_mem_left)]
      let L : Set α := {l | ∃ s ∈ S, G[G.V \ Ux].Connected l s}
      have hLV : L ⊆ G.V := by
        rintro l ⟨s, hs, hconn⟩
        exact Set.diff_subset hconn.mem_left
      have hUxFin : Ux.Finite := hUFin.union (finite_singleton x)
      have hUxncard : Ux.ncard = k := by sorry
      -- TODO: U is a separator on G - e. Then, G \ Ux ≤ (G - e) \ U. Connected.le
      have hUxSep : G.IsVxSetSeparator Ux S T := by
        sorry
      -- ...
      have hSUxSepCard : ∀ (U : Set α), U.Finite → G[L ∪ Ux].IsVxSetSeparator U S Ux → k ≤ U.ncard := by
        rintro V hVFin hVsep
        refine hsep V hVFin ?_
        rintro a ha b hb hconn
        obtain ⟨p, hpVd, rfl, rfl⟩ := Connected.iff_path.mp hconn
        have hexists : ∃ u ∈ p.val.vx, u ∉ L := by
          use p.val.finish, Walk.finish_vx_mem
          simp only [mem_setOf_eq, not_exists, not_and, L]
          rintro s hs h
          exact hUxSep s hs p.finish hb h.symm
        let w := p.val.endIf (P := fun x ↦ x ∉ L) hexists
        have hp'start : w.start = p.start := Walk.endIf_start _
        have hp'finish : w.finish ∈ Ux := by
          obtain ⟨z, hzw, hzL, f, hbtw⟩ := Walk.endIf_exists_isBetween_last hexists hpVd sorry -- TODO: w has at least 2 vertices hence nonempty
          have : w.finish ∉ L := Walk.endIf_finish hexists
          simp only [mem_setOf_eq, not_exists, not_forall, Decidable.not_not, L] at hzL this
          simp_rw [not_and] at this
          exact foo (hbtw.le (induce_le G Set.diff_subset)) hzL this
        have hp'Vd1 : w.ValidOn (G[G.V \ V]) := Walk.endIf_validOn _ hpVd
        have hp'Vd : w.ValidOn (G[(L ∪ Ux) \ V]) := by
          refine Walk.ValidOn.induce (hp'Vd1.le (induce_le G Set.diff_subset)) ?_
          rintro x hx
          refine ⟨?_, (hp'Vd1.mem_of_mem_vx hx).2⟩
          obtain hxL | rfl := Walk.endIf_mem_vx hexists hx
          · push_neg at hxL
            left
            exact hxL
          · right
            exact hp'finish
        have := Walk.connected_of_validOn_of_mem hp'Vd Walk.start_vx_mem Walk.finish_vx_mem
        specialize hVsep p.start ha w.finish hp'finish
        rw [induce_induce_eq_induce_right _ _ (Set.inter_subset_right.trans ?_), induce_V, ← hp'start] at hVsep
        exact hVsep this
        · exact Set.diff_subset
      have hFin : G[L ∪ Ux].Finite := by
        refine ⟨?_, ?_⟩
        · apply Set.Finite.union (Set.Finite.subset hfin.vx_fin ?_) hUxFin
          rintro x hx
          obtain ⟨s, hs, hconn⟩ := hx
          exact Set.diff_subset hconn.mem_left
        · exact Set.Finite.subset hfin.edge_fin (induce_E_le (L ∪ Ux))
      have htermx : (G.E ∩ {e | ∀ (x : α), G.Inc x e → x = w₁.finish ∨
        (∃ s ∈ S, G[G.V \ insert w₁.finish U].Connected x s) ∨ x ∈ U}).ncard < G.E.ncard := by
        sorry
      have := Menger_VxSet (hfin := hFin) (G[L ∪ Ux]) S Ux k hS hUxFin hSUxSepCard
      obtain ⟨Psx, hlenx, hPVdx, hPsxStartSet, hPsxFinishSet⟩ := this

      let Uy := U ∪ {y}
      have hUy : Uy ⊆ G.V := by
        simp [Uy, hUV, Set.insert_subset_iff, (Set.diff_subset hxy.vx_mem_right)]
      let R : Set α := {r | ∃ t ∈ T, G[G.V \ Uy].Connected r t}
      have hRV : R ⊆ G.V := by
        rintro r ⟨t, ht, hconn⟩
        exact Set.diff_subset hconn.mem_left
      have hUyFin : Uy.Finite := hUFin.union (finite_singleton y)
      have hUyncard : Uy.ncard = k := by sorry
      -- TODO: U is a separator on G - e. Then, G \ Uy ≤ (G - e) \ U. Connected.le
      have hUySep : G.IsVxSetSeparator Uy S T := by
        sorry
      -- ...
      have hSUySepCard : ∀ (U : Set α), U.Finite → G[R ∪ Uy].IsVxSetSeparator U Uy T → k ≤ U.ncard := by
        rintro V hVFin hVsep
        refine hsep V hVFin ?_
        rintro a ha b hb hconn
        obtain ⟨p, hpVd, rfl, rfl⟩ := Connected.iff_path.mp hconn
        have hexists : ∃ u ∈ p.val.vx, u ∉ R := by
          use p.val.start, Walk.start_vx_mem
          simp only [mem_setOf_eq, not_exists, not_and, R]
          rintro t ht h
          exact hUySep p.start ha t ht h
        sorry
        -- let w := p.val.endIf (P := fun x ↦ x ∉ R) hexists
        -- have hp'start : w.start = p.start := endIf_start _
        -- have hp'finish : w.finish ∈ Uy := by
        --   obtain ⟨z, hzw, hzL, f, hbtw⟩ := endIf_exists_isBetween_last hexists hpVd sorry -- TODO: w has at least 2 vertices hence nonempty
        --   have : w.finish ∉ R := endIf_finish hexists
        --   simp only [mem_setOf_eq, not_exists, not_forall, Decidable.not_not, R] at hzL this
        --   simp_rw [not_and] at this
        --   exact foo (hbtw.le (induce_le G Set.diff_subset)) hzL this
        -- have hp'Vd1 : w.ValidOn (G[G.V \ V]) := endIf_validOn _ hpVd
        -- have hp'Vd : w.ValidOn (G[(R ∪ Uy) \ V]) := by
        --   refine ValidOn.induce (hp'Vd1.le (induce_le G Set.diff_subset)) ?_
        --   rintro x hx
        --   refine ⟨?_, (hp'Vd1.mem_of_mem_vx hx).2⟩
        --   obtain hxL | rfl := endIf_mem_vx hexists hx
        --   · push_neg at hxL
        --     left
        --     exact hxL
        --   · right
        --     exact hp'finish
        -- have := Walk.connected_of_validOn_of_mem hp'Vd start_vx_mem finish_vx_mem
        -- specialize hVsep p.start ha w.finish hp'finish
        -- rw [induce_induce_eq_induce_right _ _ (Set.inter_subset_right.trans ?_), induce_V, ← hp'start] at hVsep
        -- exact hVsep this
        -- · exact Set.diff_subset
      have hFin : G[R ∪ Uy].Finite := by
        refine ⟨?_, ?_⟩
        · apply Set.Finite.union (Set.Finite.subset hfin.vx_fin ?_) hUyFin
          rintro x hx
          obtain ⟨s, hs, hconn⟩ := hx
          exact Set.diff_subset hconn.mem_left
        · exact Set.Finite.subset hfin.edge_fin (induce_E_le (R ∪ Uy))
      have htermy : (G.E ∩ {e | ∀ (x : α), G.Inc x e → x = w₂.start ∨
        (∃ t ∈ T, G[G.V \ insert w₂.start U].Connected x t) ∨ x ∈ U}).ncard < G.E.ncard := by
        sorry
      -- same as above
      obtain ⟨Psy, hleny, hPVdy, hPsyStartSet, hPsyFinishSet⟩ := Menger_VxSet (hfin := hFin) (G[R ∪ Uy]) Uy T k hUyFin hT hSUySepCard

      /- TODO: Now that I have two set of path ensembles, each corresponding to a unique element in
      Ux/Uy, I can append them to get a path ensemble for G. -/
      have hPsxFinishSet : Psx.FinishSet = Ux := by sorry
      have hPUStartSet : PU.StartSet = Ux := by sorry
      have hPUFinishSet : PU.FinishSet = Uy := by sorry
      have hPsyStartSet : Psy.StartSet = Uy := by sorry
      have hPsxFin : Psx.Paths.Finite := by sorry
      have hPUFin : PU.Paths.Finite := by sorry
      have hPsyFin : Psy.Paths.Finite := by sorry
      have hPsxPU : Psx.VxSet ∩ PU.VxSet = Psx.FinishSet := by
        apply le_antisymm
        · rintro z ⟨⟨px, hpx, hzpx⟩, pU, hpU, hzpU⟩
          rw [hPsxFinishSet]
          have hz1 := Walk.ValidOn.mem_of_mem_vx (hPVdx px hpx) hzpx
          have hz2 : z ∈ U ∪ {x, y} := by sorry
          sorry
        · sorry
      have hPUPsx : Psx.VxSet ∩ PU.VxSet = PU.StartSet := by
        sorry
      have hPUPsy : (Psx.append PU hPsxPU hPUPsx).VxSet ∩ Psy.VxSet = (Psx.append PU hPsxPU hPUPsx).FinishSet := by
        sorry
      have hPsyPU : (Psx.append PU hPsxPU hPUPsx).VxSet ∩ Psy.VxSet = Psy.StartSet := by
        sorry
      let P := (Psx.append PU hPsxPU hPUPsx).append Psy hPUPsy hPsyPU
      use P, ?_, ?_, ?_
      · rwa [PathEnsemble.append_finishSet]
      · rw [PathEnsemble.append_ncard_eq_right, ← PathEnsemble.StartSet_ncard, hPsyStartSet]
        exact hUyncard
        exact hPsyFin
        exact hPsyFin
      · apply PathEnsemble.append_validOn
        · apply PathEnsemble.append_validOn
          · refine hPVdx.le (induce_le G ?_)
            rintro a (ha | ha)
            · exact hLV ha
            · exact hUx ha
          · sorry
        · refine hPVdy.le (induce_le G ?_)
          rintro a (ha | ha)
          · exact hRV ha
          · exact hUy ha
      · rw [PathEnsemble.append_startSet, PathEnsemble.append_startSet]
        exact hPsxStartSet

  · rw [Set.nonempty_iff_ne_empty] at hE
    have := hsep (G.V ∩ S ∩ T) (by exact Finite.inter_of_right hT (G.V ∩ S)) ?_
    simp only [ncard_empty, nonpos_iff_eq_zero] at this
    obtain ⟨U, hU, hUcard⟩ := Set.exists_subset_card_eq this
    sorry
    sorry
    -- use ⟨Path.nil '' U, ?_⟩, ?_, ?_, ?_
    -- · rintro p ⟨x, hx, rfl⟩
    --   obtain ⟨⟨hxV, hxS⟩, hxT⟩ := hU hx
    --   exact ⟨hxS, hxT⟩
    -- · sorry -- easy
    -- · simp only
    --   rwa [Set.ncard_image_of_injective]
    --   sorry -- have a lemma that nil is injective
    -- · rintro p ⟨x, hx, rfl⟩
    --   refine Walk.nil_validOn_iff.mpr ?_
    --   exact (hU hx).1.1
    -- · sorry -- easy
termination_by 1
