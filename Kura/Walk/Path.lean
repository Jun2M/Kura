import Kura.Walk.Walk


namespace Graph
open Set Function List Nat Walk
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w1 w2 : Walk α β}

@[mk_iff]
structure IsPath (G : Graph α β) (W : Walk α β) : Prop where
  validOn : W.ValidOn G
  nodup : W.vx.Nodup

@[mk_iff]
structure IsPathFrom (G : Graph α β) (S T : Set α) (W : Walk α β) : Prop where
  validOn : W.ValidOn G
  nodup : W.vx.Nodup
  start_mem : W.start ∈ S
  finish_mem : W.finish ∈ T

lemma IsPathFrom.isWalkFrom (h : G.IsPathFrom S T w) : G.IsWalkFrom S T w := sorry


/-- A path is a walk with no duplicate vertices -/
def Path (α β : Type*) := {w : Walk α β // w.vx.Nodup}

variable {p q : Path α β} {w w1 w2 : Walk α β}
namespace Path

@[simp]
abbrev ofWalk [DecidableEq α] (w : Walk α β) : Path α β := ⟨w.dedup, w.dedup_vx_nodup⟩

/-- Create a nil path -/
@[simp]
def nil (x : α) : Path α β := ⟨Walk.nil x, by simp⟩

lemma nil_injective : Injective (nil : α → Path α β) := by
  rintro x y h
  rwa [nil, nil, ← Subtype.val_inj, nil.injEq] at h

@[simp]
lemma nil_inj : (nil x : Path α β) = nil y ↔ x = y := by
  rw [nil, nil, ← Subtype.val_inj, nil.injEq]

end Path

/-- Create a path from a single edge between two vertices -/
def Inc₂.path (hbtw : G.Inc₂ e u v) (hne : u ≠ v) : Path α β := ⟨hbtw.walk, by simp [hne]⟩

namespace Path
/-- Create the reverse of a path -/
def reverse (p : Path α β) : Path α β := ⟨p.val.reverse, by simp [p.prop]⟩

lemma ValidOn.le {p : Path α β} (h : p.val.ValidOn G) (hle : G ≤ H) : p.val.ValidOn H :=
  Walk.ValidOn.le h hle

lemma of_cons {p : Path α β} (h : p.val = Walk.cons x e w) : w.vx.Nodup := by
  have := h ▸ p.prop
  rw [cons_vx, nodup_cons] at this
  exact this.2

lemma of_prefix {p : Path α β} (h : p.val = w1.append w2)
    (heq : w1.finish = w2.start) : w1.vx.Nodup := by
  have : (w1.append w2).vx = _ ++ _ := append_vx' heq
  rw [← h] at this
  have : w1.vx.Sublist p.val.vx := by
    rw [this]
    exact sublist_append_left w1.vx w2.vx.tail
  exact this.nodup p.prop

lemma of_suffix {p : Path α β} (h : p.val = w1.append w2) : w2.vx.Nodup := by
  have : (w1.append w2).vx = _ ++ w2.vx := append_vx
  rw [← h] at this
  have : w2.vx.Sublist p.val.vx := by
    rw [this]
    exact sublist_append_right w1.vx.dropLast w2.vx
  exact this.nodup p.prop

lemma not_mem_prefix_of_mem_suffix_tail {p : Path α β} (h : p.val = w1 ++ w2)
    (heq : w1.finish = w2.start) (hmem : u ∈ w2.vx.tail) : u ∉ w1.vx := by
  have := h ▸ p.prop
  rw [append_vx' heq, nodup_append] at this
  exact (this.2.2 · hmem)

lemma not_mem_suffix_of_mem_prefix_dropLast {p : Path α β} (h : p.val = w1 ++ w2)
    (hmem : u ∈ w1.vx.dropLast) : u ∉ w2.vx := by
  have := h ▸ p.prop
  rw [append_vx, nodup_append] at this
  exact this.2.2 hmem

lemma eq_start_of_mem_prefix_suffix {p : Path α β} (h : p.val = w1 ++ w2)
    (heq : w1.finish = w2.start) (hmem1 : u ∈ w1.vx) (hmem2 : u ∈ w2.vx) :
    u = w2.start := by
  have := h ▸ p.prop
  rw [append_vx' heq, nodup_append] at this
  have := this.2.2 hmem1
  rw [← w2.vx.head_cons_tail vx_ne_nil, mem_cons, ← start_eq_vx_head] at hmem2
  simp_all only [imp_false, or_false]

lemma eq_finish_of_mem_prefix_suffix {p : Path α β} (h : p.val = w1 ++ w2)
    (heq : w1.finish = w2.start) (hmem1 : u ∈ w1.vx) (hmem2 : u ∈ w2.vx) :
    u = w1.finish := heq ▸ eq_start_of_mem_prefix_suffix h heq hmem1 hmem2

def append (p q : Path α β) (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) : Path α β :=
  ⟨p.val ++ q.val, by
    rw [append_vx]
    refine List.Nodup.append ?_ q.prop hDisj
    exact p.prop.sublist (List.dropLast_sublist p.val.vx)⟩

@[simp]
lemma append_start {p q : Path α β} (heq : p.val.finish = q.val.start)
    (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) : (p.append q hDisj).val.start = p.val.start :=
  append_start_of_eq heq

@[simp]
lemma append_finish {p q : Path α β} (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) :
    (p.append q hDisj).val.finish = q.val.finish := by
  simp only [append, Walk.append_finish]

@[simp]
lemma append_length {p q : Path α β} (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) :
    (p.append q hDisj).val.length = p.val.length + q.val.length := by
  simp only [append, Walk.append_length]

@[simp]
lemma append_vx {p q : Path α β} (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) :
    (p.append q hDisj).val.vx = p.val.vx.dropLast ++ q.val.vx := by
  simp only [append, Walk.append_vx]

@[simp]
lemma append_edge {p q : Path α β} (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) :
    (p.append q hDisj).val.edge = p.val.edge ++ q.val.edge := by
  simp only [append, Walk.append_edge]

@[simp]
lemma append_validOn {p q : Path α β} (heq : p.val.finish = q.val.start)
    (hpVd : p.val.ValidOn G) (hqVd : q.val.ValidOn G)
    (hDisj : p.val.vx.dropLast.Disjoint q.val.vx) : (p.append q hDisj).val.ValidOn G :=
  Walk.append_validOn heq hpVd hqVd



lemma edge_not_isLoop {p : Path α β} (he : e ∈ p.val.edge) (hVd : p.val.ValidOn G) : ¬ G.IsLoopAt e x := by
  intro hloop
  rw [IsLoopAt_iff_inc₂] at hloop
  obtain ⟨w₁, w₂, hw12, hnin⟩ := eq_append_cons_of_edge_mem he
  have hbtw' : G.Inc₂ e w₁.finish w₂.start := by
    simp only [ValidOn, hw12] at hVd
    obtain ⟨hbtw, H2⟩ := hVd.append_right_validOn
    exact hbtw
  have hNodup := hw12 ▸ p.prop
  simp only [Walk.append_vx, cons_vx] at hNodup
  have := List.Nodup.of_append_right hNodup
  obtain ⟨rfl, heq⟩ | ⟨rfl, heq⟩ := hloop.eq_or_eq_of_inc₂ hbtw'
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, heq, start_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this
  · rw [← w₂.vx.head_cons_tail vx_ne_nil, ← heq, start_eq_vx_head] at this
    simp only [head_cons_tail, nodup_cons, head_mem, not_true_eq_false, false_and] at this

lemma ne_of_inc₂_edge_mem (hVd : p.val.ValidOn G) (hbtw : G.Inc₂ e u v)
    (he : e ∈ p.val.edge) : u ≠ v := by
  rintro huv
  refine edge_not_isLoop (x := v) he hVd ?_
  rw [IsLoopAt_iff_inc₂]
  exact huv ▸ hbtw

@[simp]
lemma start_not_mem_vx_tail {p : Path α β} : p.val.start ∉ p.val.vx.tail := by
  rintro hmem
  have := p.prop
  rw [← p.val.vx.head_cons_tail vx_ne_nil, List.nodup_cons] at this
  exact this.1 (start_eq_vx_head ▸ hmem)

@[simp]
lemma finish_not_mem_vx_dropLast {p : Path α β} : p.val.finish ∉ p.val.vx.dropLast := by
  rintro hmem
  have := p.prop
  rw [← p.val.vx.dropLast_append_getLast vx_ne_nil, ← List.concat_eq_append,
    List.nodup_concat] at this
  exact this.2 (finish_eq_vx_getLast ▸ hmem)

@[simp]
lemma start_eq_finish_iff : p.val.start = p.val.finish ↔ ¬ p.val.Nonempty := by
  obtain ⟨w, hw⟩ := p
  simp only [start_eq_finish_iff hw, Nonempty.not_iff]

@[simp]
lemma start_ne_finish_iff : p.val.start ≠ p.val.finish ↔ p.val.Nonempty :=
  start_eq_finish_iff.not_left

end Path

@[simp]
lemma Inc₂.path_start (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.start = u := by simp only [path, Walk.start]

@[simp]
lemma Inc₂.path_finish (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.finish = v := by simp only [path, Walk.finish]

@[simp]
lemma Inc₂.path_length (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.length = 1 := by simp only [path, Walk.length]

@[simp]
lemma Inc₂.path_vx (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.vx = [u, v] := by simp only [path, Walk.vx]

@[simp]
lemma Inc₂.path_edge (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.edge = [e] := by simp only [path, Walk.edge]

@[simp]
lemma Inc₂.path_validOn (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.ValidOn G := walk_validOn hbtw

@[simp]
lemma Inc₂.path_validOn' (hbtw : G.Inc₂ e u v) (hne : u ≠ v) :
    (Inc₂.path hbtw hne).val.ValidOn (G[{u, v}]) := by
  refine (path_validOn hbtw hne).induce ?_
  rintro x hx
  simpa [Inc₂.path] using hx

lemma Connected.iff_path :
  G.Connected u v ↔ ∃ p : Path α β, p.val.ValidOn G ∧ p.val.start = u ∧ p.val.finish = v := by
  classical
  rw [Connected.iff_walk]
  constructor
  · rintro ⟨w, hwVd, rfl, rfl⟩
    use Path.ofWalk w, dedup_validOn hwVd, dedup_start w, dedup_finish w
  · rintro ⟨p, hpVd, rfl, rfl⟩
    use p.val, hpVd, rfl

lemma Contract.path {α' : Type*} {w : Walk α' β} {p : α → α'} {C : Set β} (hVd : ValidOn G p C)
    (h : w.ValidOn (G /[p] C)) : ∀ x ∈ G.V, ∀ y ∈ G.V, p x = w.start → p y = w.finish →
    ∃ p' : Path α β, p'.val.ValidOn G ∧ p'.val.start = x ∧ p'.val.finish = y ∧
    {e | e ∈ p'.val.edge} ⊆ {e | e ∈ w.edge ∨ e ∈ C} := by
  classical
  rintro x hx y hy hpx hpy
  obtain ⟨w', hw'Vd, rfl, rfl, hsub⟩ := Contract.walk hVd h x hx y hy hpx hpy
  use Path.ofWalk w', dedup_validOn hw'Vd, dedup_start w', dedup_finish w',
    Subset.trans (dedup_edge_sublist w') hsub


-- /-- If the endpoints of a path are connected in G via a valid path, they are connected in G -/
-- lemma connected_of_validOn (h : p.ValidOn G u v) : G.Connected u v :=
--   Walk.connected_of_validOn h

namespace Path
section disjoint

/-- A collection of paths is internally disjoint if no vertex appears in more than one path
  except for the special two vertices u and v. (i.e. the endpoints of the paths. But this is not
  enforced in the definition) -/
def InternallyDisjoint (u v : α) (Ps : Set (Path α β)) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.val.vx → x ∈ pj.val.vx → pi ≠ pj → x = u ∨ x = v

/-- A collection of paths is disjoint if no vertex appears in more than one path -/
def Disjoint (Ps : Set (Path α β)) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.val.vx → x ∈ pj.val.vx → pi = pj

end disjoint

end Path
