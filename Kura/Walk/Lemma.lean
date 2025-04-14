import Kura.Walk.Operation
import Kura.Walk.Dedup
import Kura.Operation.Minor
import Kura.Walk.Subgraph


namespace Graph
open Set Function List Nat Walk
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w1 w2 : Walk α β}


namespace Walk

lemma firstAt_isSuffix [DecidableEq α] (hx : x ∈ w) : ∃ w' : Walk α β, w' ++ (w.firstAt x hx) = w := by
  induction w generalizing x with
  | nil u =>
    rw [mem_nil_iff] at hx
    subst u
    use nil x
    rfl
  | cons u e W ih =>
    rw [mem_cons_iff] at hx
    unfold firstAt
    by_cases h : x ∈ W
    · simp only [h, ↓reduceDIte]
      obtain ⟨w', hw'⟩ := ih h
      use cons u e w'
      simp [hw']
    · simp only [h, or_false, ↓reduceDIte, append_left_eq_self, Nonempty.not_iff] at hx ⊢
      subst u
      use nil x, x

lemma endIf_dropLast_mem_vx {P : α → Prop} [DecidablePred P] {w : Walk α β} (h : ∃ u ∈ w, P u)
    (hNonempty : (w.endIf h).Nonempty) (hu : u ∈ (w.endIf h).dropLast) : ¬ P u := by
  match w with
  | .nil x => simp_all only [endIf_nil, Nonempty.not_nil]
  | .cons x e (nil y) =>
    simp_all only [endIf_cons, endIf_nil, dite_eq_ite, dropLast_vx]
    split_ifs at hu with hPx
    · simp_all only [cons_vx, nil_vx, mem_cons, not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, true_or, ite_true, Nonempty.not_nil]
    · simp_all only [mem_cons_iff, mem_nil_iff, exists_eq_or_imp, exists_eq_left, false_or,
      ite_false, Nonempty.cons_true, dropLast_cons_nil, not_false_eq_true]
  | .cons x e (cons y e' w) =>
    by_cases hPx : P x
    · simp_all
    · by_cases hxu : u = x
      · simp_all
      · obtain ⟨v, hv, hv2⟩ := h
        rw [mem_cons_iff] at hv
        obtain rfl | hvmem := hv
        · simp_all
        · have hexists : ∃ u ∈ (cons y e' w), P u := by use v
          by_cases hnonempty : ((cons y e' w).endIf hexists).Nonempty
          · refine endIf_dropLast_mem_vx (w := cons y e' w) (by use v) hnonempty ?_
            by_cases hPy : P y
            · simp only [endIf_cons, hPx, ↓reduceDIte, hPy, dropLast_cons_nil, mem_nil_iff,
              hxu] at hu
            · simpa [hPx, hPy, hxu] using hu
          · simp only [Nonempty.not_iff] at hnonempty
            obtain ⟨a, ha⟩ := hnonempty
            simp_all

end Walk

namespace IsPath

lemma edge_not_isLoop (hP : G.IsPath w) (he : e ∈ w.edge) : ¬ G.IsLoopAt e x := by
  rw [IsLoopAt_iff_inc₂]
  obtain ⟨w₁, w₂, rfl, hnin⟩ := eq_append_cons_of_edge_mem he
  have hbtw' : G.Inc₂ e w₁.last w₂.first := hP.validIn.append_right_validIn.1
  have hNodup := hP.nodup
  rw [Walk.append_vx, cons_vx] at hNodup
  have := List.Nodup.of_append_right hNodup
  rintro hloop
  obtain ⟨rfl, heq⟩ | ⟨rfl, heq⟩ := hloop.eq_or_eq_of_inc₂ hbtw'
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, heq, first_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, ← heq, first_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this

lemma ne_of_inc₂_edge_mem (hP : G.IsPath w) (hbtw : G.Inc₂ e u v) (he : e ∈ w.edge) : u ≠ v := by
  refine fun huv ↦ edge_not_isLoop (x := v) hP he ?_
  rw [IsLoopAt_iff_inc₂]
  exact huv ▸ hbtw

@[simp]
lemma first_not_mem_vx_tail (hP : G.IsPath w) : w.first ∉ w.vx.tail := by
  have := hP.nodup
  rw [← w.vx.head_cons_tail vx_ne_nil, List.nodup_cons] at this
  exact fun a ↦ this.1 (first_eq_vx_head ▸ a)

@[simp]
lemma last_not_mem_vx_dropLast (hP : G.IsPath w) : w.last ∉ w.vx.dropLast := by
  have := hP.nodup
  rw [← w.vx.dropLast_append_getLast vx_ne_nil, ← List.concat_eq_append, List.nodup_concat] at this
  exact fun a ↦ this.2 (last_eq_vx_getLast ▸ a)

@[simp]
lemma first_eq_last_iff (hP : G.IsPath w) : w.first = w.last ↔ ¬ w.Nonempty := by
  induction w with
  | nil => simp
  | cons v e w ih =>
    simp only [cons_first, cons_last, Nonempty.cons_true, not_true_eq_false, iff_false]
    rintro rfl
    simp at hP

@[simp]
lemma first_ne_last_iff (hP : G.IsPath w) : w.first ≠ w.last ↔ w.Nonempty :=
  (first_eq_last_iff hP).not_left

end IsPath

lemma Connected.iff_path : G.Connected u v ↔
    ∃ w : Walk α β, G.IsPath w ∧ w.first = u ∧ w.last = v := by
  classical
  rw [Connected.iff_walk]
  constructor
  · rintro ⟨w, hP, rfl, rfl⟩
    use w.dedup, dedup_isPath hP, dedup_first w, dedup_last w
  · rintro ⟨w, hP, rfl, rfl⟩
    use w, hP.validIn

-- noncomputable def Contract.walk {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β}
--     (hVd : ValidIn G p C) (h : w.ValidIn (G /[p] C)) {x y : α} (hx : x ∈ G.V) (hy : y ∈ G.V)
--     (hpx : p x = w.first) (hpy : p y = w.last) : Walk α β :=
--   match w with
--   | .nil u => ((hVd hx hy).mp <| hpx.trans hpy.symm).symm.exist_walk.choose
--   | .cons u e W => by
--     have hw : (Walk.cons u e W).ValidIn ((G /[p] C){{e | e ∈ (Walk.cons u e W).edge}}) :=
--       ValidIn.restrict _ _ h (by simp)
--     simp only [cons_first, cons_last] at hpx hpy
--     simp only [cons_edge, mem_cons, cons_validIn_iff, restrict_inc₂, Inc₂, mem_setOf_eq,
--       true_or, and_true] at hw
--     simp only [cons_validIn_iff, Inc₂] at h
--     obtain ⟨H, _hVdW⟩ := hw
--     choose z hrfl a ha hbtw he using H
--     subst hrfl
--     rw [hVd hx hbtw.vx_mem_left] at hpx
--     let w' := hpx.exist_walk.choose
--     exact w'.append (Walk.cons w'.last e <| walk hVd h.2 hbtw.vx_mem_right hy ha hpy)

-- noncomputable def Contract.walk {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β}
--     (hVd : ValidIn G p C) (h : w.ValidIn (G /[p] C)) :
--     ∀ x ∈ G.V, ∀ y ∈ G.V, p x = w.first → p y = w.last → Walk α β := by
--   induction w with
--   | nil u =>
--     rintro x hx y hy hpx hpy
--     simp only [nil_first, nil_last] at hpx hpy
--     subst u
--     rw [hVd hy hx] at hpy
--     exact hpy.symm.exist_walk.choose
--   | cons u e W ih =>
--     rintro x hx y hy hpx hpy
--     have hw : (Walk.cons u e W).ValidIn ((G /[p] C){{e | e ∈ (Walk.cons u e W).edge}}) := by
--       apply ValidIn.restrict _ _ h ?_
--       simp
--     simp only [cons_first, cons_last] at hpx hpy
--     simp only [cons_edge, mem_cons, cons_validIn_iff, restrict_inc₂, Inc₂, mem_setOf_eq,
--       true_or, and_true] at hw
--     simp only [cons_validIn_iff, Inc₂] at h
--     obtain ⟨H, _hVdW⟩ := hw
--     choose z hrfl a ha hbtw he using H
--     subst hrfl
--     rw [hVd hx hbtw.vx_mem_left] at hpx
--     let w' := hpx.exist_walk.choose
--     exact w'.append (Walk.cons w'.last e <| ih h.2 a hbtw.vx_mem_right y hy ha hpy)

-- lemma Contract.walk_validIn {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β}
--     (hVd : ValidIn G p C) (h : w.ValidIn (G /[p] C)) (hx : x ∈ G.V) (hy : y ∈ G.V)
--     (hpx : p x = w.first) (hpy : p y = w.last) :
--     (Contract.walk hVd h hx hy hpx hpy).ValidIn G := by
--   match w with
--   | .nil u =>
--     unfold Contract.walk
--     obtain ⟨H1, H2, H3⟩ := ((hVd hx hy).mp <| hpx.trans hpy.symm).symm.exist_walk.choose_spec
--     exact H1.le (restrict_le _ _)
--   | .cons u e W =>
--     have hw : (Walk.cons u e W).ValidIn ((G /[p] C){{e | e ∈ (Walk.cons u e W).edge}}) :=
--       ValidIn.restrict _ _ h (by simp)
--     simp only [cons_first, cons_last] at hpx hpy
--     simp only [cons_edge, mem_cons, cons_validIn_iff, restrict_inc₂, Inc₂, mem_setOf_eq,
--       true_or, and_true] at hw
--     simp only [cons_validIn_iff, Inc₂] at h
--     obtain ⟨H, _hVdW⟩ := hw
--     choose z hrfl a ha hbtw he using H
--     subst hrfl
--     rw [hVd hx hbtw.vx_mem_left] at hpx
--     let w' := hpx.exist_walk.choose
--     unfold Contract.walk
--     -- change (w'.append (Walk.cons w'.last e <| walk hVd h.2 hbtw.vx_mem_right hy ha hpy)).ValidIn G
--     sorry

lemma Contract.walk {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β} (hVd : ValidIn G p C)
    (h : w.ValidIn (G /[p] C)) : ∀ x ∈ G.V, ∀ y ∈ G.V, p x = w.first → p y = w.last →
    ∃ w' : Walk α β, w'.ValidIn G ∧ w'.first = x ∧ w'.last = y ∧
    {e | e ∈ w'.edge} ⊆ {e | e ∈ w.edge ∨ e ∈ C} := by
  induction w with
  | nil u =>
    rintro x hx y hy hpx hpy
    simp only [nil_first, nil_last] at hpx hpy
    subst u
    rw [hVd hy hx] at hpy
    obtain ⟨w, hwVd, rfl, rfl⟩ := hpy.symm.exist_walk
    use w, ?_, rfl, rfl
    · simp only [nil_edge, not_mem_nil, false_or, setOf_mem_eq]
      rintro e he
      have := hwVd.edge_mem_of_mem he
      exact Set.mem_of_mem_inter_right this
    · exact hwVd.le (restrict_le _ _)
  | cons u e W ih =>
    rintro x hx y hy hpx hpy
    have hw : (Walk.cons u e W).ValidIn ((G /[p] C){{e | e ∈ (Walk.cons u e W).edge}}) := by
      apply ValidIn.restrict h ?_
      simp
    simp only [cons_first, cons_last] at hpx hpy
    simp only [cons_edge, mem_cons, cons_validIn, restrict_inc₂, Inc₂, mem_setOf_eq,
      true_or, and_true] at hw
    simp only [cons_validIn, Inc₂] at h
    obtain ⟨⟨z, rfl, a, ha, hbtw, he⟩, hVdW⟩ := hw
    obtain ⟨_B, hVdWp⟩ := h
    rw [hVd hx hbtw.vx_mem_left] at hpx
    obtain ⟨w, hVdw, rfl, rfl, hsu⟩ := ih hVdWp a hbtw.vx_mem_right y hy ha hpy
    obtain ⟨w', hw'Vd, rfl, rfl⟩ := hpx.exist_walk
    use w' ++ (cons w'.last e w), ?_, by simp, by simp
    · simp +contextual only [append_edge, cons_edge, mem_append, mem_cons, setOf_subset_setOf]
      rintro f (hfw' | rfl | hfw)
      · right
        have := hw'Vd.edge_mem_of_mem hfw'
        exact Set.mem_of_mem_inter_right this
      · tauto
      · obtain (h1 | h2) := hsu hfw <;> tauto
    · refine append_validIn (by simp) (hw'Vd.le (restrict_le _ _)) ?_
      simp [hVdw, hbtw]

lemma Contract.map_walk_of_walk {α' : Type*} {w : Walk α β} {p : α → α'} {C : Set β}
    (hVd : ValidIn G p C) (h : w.ValidIn G) : ∃ w' : Walk α' β, w'.ValidIn (G /[p] C) ∧
    w'.first = p w.first ∧ w'.last = p w.last ∧ {e | e ∈ w'.edge} ⊆ {e | e ∈ w.edge} := by
  induction w with
  | nil u =>
    use nil (p u), ?_, rfl, rfl, by simp
    use u, h
  | cons u e W ih =>
    obtain ⟨hbtw, hVdW⟩ := h
    obtain ⟨w', hw'Vd, hst, hfin, hsub⟩ := ih hVdW
    by_cases he : e ∈ C
    · have : p u = w'.first := by
        rw [hst, hVd hbtw.vx_mem_left hbtw.vx_mem_right]
        apply Inc₂.connected
        rw [restrict_inc₂]
        exact ⟨hbtw, he⟩
      use w', hw'Vd, this.symm, hfin
      simp only [cons_edge, mem_cons, setOf_subset_setOf]
      exact fun a a_1 ↦ Or.symm (Or.intro_left (a = e) (hsub a_1))
    · use (Walk.cons (p u) e w'), ?_, by simp, by simp [hfin]
      · simp only [cons_edge, mem_cons, setOf_subset_setOf, forall_eq_or_imp, true_or, true_and]
        rintro f hfw'
        right
        exact hsub hfw'
      · simp only [hw'Vd, cons_validIn, Inc₂, and_true]
        use u, rfl, W.first, hst.symm, hbtw

lemma Contract.path {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β} (hVd : ValidIn G p C)
    (h : w.ValidIn (G /[p] C)) : ∀ x ∈ G.V, ∀ y ∈ G.V, p x = w.first → p y = w.last →
    ∃ p' : Walk α β, G.IsPath p' ∧ p'.first = x ∧ p'.last = y ∧ p'.edgeSet ⊆ w.edgeSet ∪ C := by
  classical
  rintro x hx y hy hpx hpy
  obtain ⟨w', hw'Vd, rfl, rfl, hsub⟩ := Contract.walk hVd h x hx y hy hpx hpy
  use w'.dedup, dedup_isPath hw'Vd, dedup_first w', dedup_last w',
    Subset.trans (dedup_edge_sublist w') hsub

-- /-- If the endpoints of a path are connected in G via a valid path, they are connected in G -/
-- lemma connected_of_validIn (h : p.ValidIn G u v) : G.Connected u v :=
--   Walk.connected_of_validIn h

noncomputable def dist {G : Graph α β} {u v : α} (h : G.Connected u v) : ℕ := by
  classical
  exact Nat.find (by
    obtain ⟨w, hwVd, rfl, rfl⟩ := h.exist_walk
    use w.length, w, hwVd
    : ∃ n, ∃ w : Walk α β, w.ValidIn G ∧ w.first = u ∧ w.last = v ∧ w.length = n)
