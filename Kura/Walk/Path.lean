import Kura.Walk.Operation


namespace Graph
open Set Function List Nat Walk
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w1 w2 : Walk α β}

namespace Path

lemma not_mem_prefix_of_mem_suffix_tail {p : Path α β} (h : p.val = w1 ++ w2)
    (heq : w1.last = w2.first) (hmem : u ∈ w2.vx.tail) : u ∉ w1.vx := by
  have := h ▸ p.prop
  rw [append_vx' heq, nodup_append] at this
  exact (this.2.2 · hmem)

lemma not_mem_suffix_of_mem_prefix_dropLast {p : Path α β} (h : p.val = w1 ++ w2)
    (hmem : u ∈ w1.vx.dropLast) : u ∉ w2.vx := by
  have := h ▸ p.prop
  rw [append_vx, nodup_append] at this
  exact this.2.2 hmem

lemma eq_first_of_mem_prefix_suffix {p : Path α β} (h : p.val = w1 ++ w2)
    (heq : w1.last = w2.first) (hmem1 : u ∈ w1.vx) (hmem2 : u ∈ w2.vx) :
    u = w2.first := by
  have := h ▸ p.prop
  rw [append_vx' heq, nodup_append] at this
  have := this.2.2 hmem1
  rw [← w2.vx.head_cons_tail vx_ne_nil, mem_cons, ← first_eq_vx_head] at hmem2
  simp_all only [imp_false, or_false]

lemma eq_last_of_mem_prefix_suffix {p : Path α β} (h : p.val = w1 ++ w2)
    (heq : w1.last = w2.first) (hmem1 : u ∈ w1.vx) (hmem2 : u ∈ w2.vx) :
    u = w1.last := heq ▸ eq_first_of_mem_prefix_suffix h heq hmem1 hmem2


lemma edge_not_isLoop {p : Path α β} (he : e ∈ p.val.edge) (hVd : p.val.ValidIn G) : ¬ G.IsLoopAt e x := by
  intro hloop
  rw [IsLoopAt_iff_inc₂] at hloop
  obtain ⟨w₁, w₂, hw12, hnin⟩ := eq_append_cons_of_edge_mem he
  have hbtw' : G.Inc₂ e w₁.last w₂.first := by
    simp only [ValidIn, hw12] at hVd
    obtain ⟨hbtw, H2⟩ := hVd.append_right_validIn
    exact hbtw
  have hNodup := hw12 ▸ p.prop
  simp only [Walk.append_vx, cons_vx] at hNodup
  have := List.Nodup.of_append_right hNodup
  obtain ⟨rfl, heq⟩ | ⟨rfl, heq⟩ := hloop.eq_or_eq_of_inc₂ hbtw'
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, heq, first_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, ← heq, first_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this

lemma ne_of_inc₂_edge_mem (hVd : p.val.ValidIn G) (hbtw : G.Inc₂ e u v)
    (he : e ∈ p.val.edge) : u ≠ v := by
  rintro huv
  refine edge_not_isLoop (x := v) he hVd ?_
  rw [IsLoopAt_iff_inc₂]
  exact huv ▸ hbtw

@[simp]
lemma first_not_mem_vx_tail {p : Path α β} : p.val.first ∉ p.val.vx.tail := by
  rintro hmem
  have := p.prop
  rw [← p.val.vx.head_cons_tail vx_ne_nil, List.nodup_cons] at this
  exact this.1 (first_eq_vx_head ▸ hmem)

@[simp]
lemma last_not_mem_vx_dropLast {p : Path α β} : p.val.last ∉ p.val.vx.dropLast := by
  rintro hmem
  have := p.prop
  rw [← p.val.vx.dropLast_append_getLast vx_ne_nil, ← List.concat_eq_append,
    List.nodup_concat] at this
  exact this.2 (last_eq_vx_getLast ▸ hmem)

@[simp]
lemma first_eq_last_iff : p.val.first = p.val.last ↔ ¬ p.val.Nonempty := by
  obtain ⟨w, hw⟩ := p
  simp only [first_eq_last_iff hw, Nonempty.not_iff]

@[simp]
lemma first_ne_last_iff : p.val.first ≠ p.val.last ↔ p.val.Nonempty :=
  first_eq_last_iff.not_left

end Path

lemma Connected.iff_path :
  G.Connected u v ↔ ∃ p : Path α β, p.val.ValidIn G ∧ p.val.first = u ∧ p.val.last = v := by
  classical
  rw [Connected.iff_walk]
  constructor
  · rintro ⟨w, hwVd, rfl, rfl⟩
    use Path.ofWalk w, dedup_validIn hwVd, dedup_first w, dedup_last w
  · rintro ⟨p, hpVd, rfl, rfl⟩
    use p.val, hpVd, rfl

lemma Contract.path {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β} (hVd : ValidIn G p C)
    (h : w.ValidIn (G /[p] C)) : ∀ x ∈ G.V, ∀ y ∈ G.V, p x = w.first → p y = w.last →
    ∃ p' : Path α β, p'.val.ValidIn G ∧ p'.val.first = x ∧ p'.val.last = y ∧
    {e | e ∈ p'.val.edge} ⊆ {e | e ∈ w.edge ∨ e ∈ C} := by
  classical
  rintro x hx y hy hpx hpy
  obtain ⟨w', hw'Vd, rfl, rfl, hsub⟩ := Contract.walk hVd h x hx y hy hpx hpy
  use Path.ofWalk w', dedup_validIn hw'Vd, dedup_first w', dedup_last w',
    Subset.trans (dedup_edge_sublist w') hsub


-- /-- If the endpoints of a path are connected in G via a valid path, they are connected in G -/
-- lemma connected_of_validIn (h : p.ValidIn G u v) : G.Connected u v :=
--   Walk.connected_of_validIn h
