import Kura.WList.Sublist
import Kura.Le

/-
This file defined predicates stating that an abstract walk `w` is a walk/trail/path of a graph `G`.
-/

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
  {w w₁ w₂ : WList α β} {S T : Set α}

open Graph WList List Set

namespace Graph

/-- `G.IsWalk w` means that `w : WList α β` is a walk of `G : Graph α β`. -/
inductive IsWalk (G : Graph α β) : WList α β → Prop
  | nil {x} (hx : x ∈ G.V) : G.IsWalk (nil x)
  | cons {x e w} (hw : G.IsWalk w) (h : G.Inc₂ e x w.first) : G.IsWalk (cons x e w)

@[simp]
lemma nil_isWalk_iff : G.IsWalk (nil x) ↔ x ∈ G.V :=
  ⟨fun h ↦ by cases h with | _ => simp_all, IsWalk.nil⟩

@[simp]
lemma cons_isWalk_iff : G.IsWalk (cons x e w) ↔ G.Inc₂ e x w.first ∧ G.IsWalk w :=
  ⟨fun h ↦ by cases h with | _ => simp_all, fun h ↦ h.2.cons h.1⟩

@[simp]
lemma IsWalk.of_cons (hw : G.IsWalk (.cons x e w)) : G.IsWalk w := by
  simp_all

lemma IsWalk.vx_mem_of_mem (h : G.IsWalk w) (hmem : x ∈ w) : x ∈ G.V := by
  induction h with | nil => simp_all | @cons y f w hw h ih =>
    simp_all only [mem_cons_iff]
    exact hmem.elim (fun h' ↦ h' ▸ h.vx_mem_left) ih

lemma IsWalk.edge_mem_of_mem (h : G.IsWalk w) (hmem : e ∈ w.edge) : e ∈ G.E := by
  induction h with | nil => simp_all | @cons x f w hw h ih =>
    simp_all only [cons_edge, mem_cons]
    exact hmem.elim (fun h' ↦ h' ▸ h.edge_mem) ih

lemma IsWalk.vx_mem_of_edge_mem (h : G.IsWalk w) (he : e ∈ w.edge) (heu : G.Inc e u) : u ∈ w := by
  induction h with
  | nil => simp at he
  | @cons x f w hw h ih =>
    simp_all only [cons_edge, mem_cons, mem_cons_iff]
    refine he.elim ?_ fun h' ↦ .inr <| ih h'
    rintro rfl
    obtain rfl | rfl := h.eq_of_inc heu <;> simp

lemma IsWalk.vxSet_subset (hVd : G.IsWalk w) : w.vxSet ⊆ G.V :=
  fun _ ↦ hVd.vx_mem_of_mem

lemma IsWalk.edgeSet_subset (h : G.IsWalk w) : w.edgeSet ⊆ G.E := fun _ ↦ h.edge_mem_of_mem

lemma IsWalk.mem_of_mem_edge_of_inc (hw : G.IsWalk w) (he : e ∈ w.edge) (h : G.Inc e u) :
    u ∈ w := by
  induction w with
  | nil x => simp at he
  | cons x e' w ih =>
    simp_all only [forall_const, cons_edge, mem_cons, mem_cons_iff, cons_isWalk_iff]
    obtain rfl | he := he
    · obtain rfl | rfl := hw.1.eq_of_inc h <;> simp
    exact .inr (ih he)

lemma IsWalk.sublist (hw₂ : G.IsWalk w₂) (h : w₁.IsSublist w₂) : G.IsWalk w₁ := by
  induction h with
  | nil h => simp [hw₂.vx_mem_of_mem h]
  | cons x e h ih => exact ih hw₂.of_cons
  | cons₂ x e h h_eq ih =>
    rw [cons_isWalk_iff] at hw₂ ⊢
    rw [h_eq]
    exact ⟨hw₂.1, ih hw₂.2⟩

lemma IsWalk.prefix (hw : G.IsWalk w) (h : w₁.IsPrefix w) : G.IsWalk w₁ :=
  hw.sublist h.isSublist

lemma IsWalk.suffix (hw : G.IsWalk w) (h : w₁.IsSuffix w) : G.IsWalk w₁ :=
  hw.sublist h.isSublist

lemma IsWalk.append (h₁ : G.IsWalk w₁) (h₂ : G.IsWalk w₂) (h : w₁.last = w₂.first) :
  G.IsWalk (w₁ ++ w₂) := by
  induction h₁ with simp_all

lemma IsWalk.concat (h : G.IsWalk w) (he : G.Inc₂ e w.last x) : G.IsWalk (w.concat e x) := by
  induction h with simp_all [he.vx_mem_right]

lemma IsWalk.of_append_left (h : G.IsWalk (w₁ ++ w₂)) (h_eq : w₁.last = w₂.first) :
    G.IsWalk w₁ :=
  h.prefix <| isPrefix_append_right h_eq

lemma IsWalk.of_append_right (h : G.IsWalk (w₁ ++ w₂)) : G.IsWalk w₂ :=
  h.suffix <| isSuffix_append_left ..

lemma IsWalk.last_eq_first (h : G.IsWalk (w₁ ++ w₂)) (hw₁ : G.IsWalk w₁) (hne : w₁.Nonempty) :
    w₁.last = w₂.first := by
  induction hw₁ with
  | nil => simp_all
  | @cons x e w hw h' IH => cases w with
    | nil u =>
      simp only [nil_first, WList.cons_append, WList.nil_append, cons_isWalk_iff] at h' h
      exact h'.inc₂_iff_eq_right.mp h.1
    | cons => simp_all

lemma IsWalk.reverse (hw : G.IsWalk w) : G.IsWalk w.reverse := by
  induction hw with
  | nil => simp_all
  | cons hw h ih =>
    simp_all only [WList.reverse_cons]
    apply ih.concat <| by simpa using h.symm

@[simp]
lemma isWalk_reverse_iff : G.IsWalk w.reverse ↔ G.IsWalk w :=
  ⟨fun h ↦ by simpa using h.reverse, IsWalk.reverse⟩

lemma IsWalk.of_le (h : H.IsWalk w) (hle : H ≤ G) : G.IsWalk w := by
  induction h with
  | nil hx => simp [vx_subset_of_le hle hx]
  | cons _ h ih => simp [ih, h.of_le hle]

lemma IsWalk.inc₂_of_inc₂ (h : G.IsWalk w) (hexy : w.Inc₂ e x y) : G.Inc₂ e x y := by
  induction hexy with
  | cons_left => simp_all
  | cons_right => exact Inc₂.symm <| by simp_all
  | cons => simp_all

lemma IsWalk.inc₂_of_dInc (h : G.IsWalk w) (hexy : w.DInc e x y) : G.Inc₂ e x y :=
  h.inc₂_of_inc₂ hexy.inc₂

lemma IsWalk.wellFormed (h : G.IsWalk w) : w.WellFormed := by
  induction w with
  | nil u => simp [WellFormed]
  | cons u e w ih =>
    simp only [cons_isWalk_iff] at h
    rw [cons_wellFormed_iff, and_iff_right (ih h.2)]
    exact fun y₁ y₂ h' ↦ (h.2.inc₂_of_inc₂ h').sym2_eq_iff.1 h.1

/-- `G.IsWalkFrom S T w` means that `w` is a walk of `G` with one end in `S` and the other in `T`.-/
@[mk_iff]
structure IsWalkFrom (G : Graph α β) (S T : Set α) (w : WList α β) : Prop where
  isWalk : G.IsWalk w
  first_mem : w.first ∈ S
  last_mem : w.last ∈ T

lemma IsWalkFrom.reverse (h : G.IsWalkFrom S T w) : G.IsWalkFrom T S w.reverse where
  isWalk := h.isWalk.reverse
  first_mem := by simp [h.last_mem]
  last_mem := by simp [h.first_mem]





/-- The walk corresponding to an incidence `G.Inc₂ e u v`. -/
def Inc₂.walk (_h : G.Inc₂ e u v) : WList α β := cons u e (nil v)

namespace Inc₂

@[simp]
lemma walk_first (h : G.Inc₂ e u v): h.walk.first = u := rfl

@[simp]
lemma walk_last (h : G.Inc₂ e u v): h.walk.last = v := rfl

@[simp] lemma walk_nonempty (h : G.Inc₂ e u v): h.walk.Nonempty := by simp [walk]

@[simp]
lemma walk_vx (h : G.Inc₂ e u v): h.walk.vx = [u, v] := rfl

lemma mem_walk_iff (h : G.Inc₂ e u v) (x : α) : x ∈ h.walk ↔ x = u ∨ x = v := by
  simp [walk]

@[simp]
lemma walk_vxSet (h : G.Inc₂ e u v): h.walk.vxSet = {u, v} := by
  simp [mem_walk_iff, Set.ext_iff]

@[simp]
lemma walk_edge (h : G.Inc₂ e u v): h.walk.edge = [e] := rfl

@[simp]
lemma walk_edgeSet (h : G.Inc₂ e u v): h.walk.edgeSet = {e} := by
  simp [edgeSet]

@[simp]
lemma walk_length (h : G.Inc₂ e u v): h.walk.length = 1 := rfl

@[simp]
lemma walk_isWalk (h : G.Inc₂ e u v) : G.IsWalk h.walk := by
  simp [walk, h, h.vx_mem_right]


end Inc₂

lemma length_eq_one_iff : w.length = 1 ∧ G.IsWalk w ↔ ∃ x e y h, w = (h : G.Inc₂ e x y).walk := by
  refine ⟨fun ⟨hlen, hVd⟩ ↦ ?_, fun ⟨x, e, y, h, heq⟩ ↦ by simp [heq]⟩
  obtain ⟨x, e, w', rfl, hlenw'⟩ := length_eq_succ_iff.mp hlen
  obtain ⟨y, rfl⟩ := nil_iff_eq_nil.mp <| WList.length_eq_zero.mp hlenw'
  simp only [cons_isWalk_iff, nil_first, nil_isWalk_iff] at hVd
  exact ⟨x, e, y, hVd.1, by simp [Inc₂.walk]⟩



-- lemma IsPath.prefix (hP : G.IsPath w) (hPf : w₁.IsPrefix w) : G.IsPath w₁ := by
--   refine ⟨hP.isWalk.prefix hPf, ?_⟩

  -- obtain ⟨w₂, heq, rfl⟩ := hPf.exists_eq_append
  -- exact append_left_isPath heq hP



-- lemma append_isWalkFrom (h : w₁.last = w₂.first) (h₁ : G.IsWalkFrom S T w₁)
--     (h₂ : G.IsWalkFrom T U w₂) : G.IsWalkFrom S U (w₁ ++ w₂) := by
--   obtain ⟨hw₁Vd, hw₁first, hw₁last⟩ := h₁
--   obtain ⟨hw₂Vd, hw₂first, hw₂last⟩ := h₂
--   refine ⟨?_, ?_, ?_⟩
--   · exact WList.append_isWalk h hw₁Vd hw₂Vd
--   · simpa [h]
--   · simpa



-- lemma append_isPath (h : w₁.last = w₂.first) (h₁ : G.IsPath w₁) (h₂ : G.IsPath w₂)
--     (hvxSet : w₁.vxSet ∩ w₂.vxSet ⊆ {w₁.last}) : G.IsPath (w₁ ++ w₂) where
--   isWalk := append_isWalk h h₁.isWalk h₂.isWalk
--   nodup := by
--     simp only [Set.subset_singleton_iff, Set.mem_inter_iff, mem_vxSet_iff, and_imp, append_vx,
--       nodup_append, h₁.nodup.sublist w₁.vx.dropLast_sublist, h₂.nodup, true_and] at hvxSet ⊢
--     rintro x hx₁ hx₂
--     obtain rfl := hvxSet x (List.mem_of_mem_dropLast hx₁) hx₂
--     /- This should be its own lemma -/
--     have aux {l : List α} (hl : l ≠ []) (hl' : l.Nodup) : l.getLast hl ∉ l.dropLast := by
--       rw [← dropLast_append_getLast hl, nodup_append] at hl'
--       obtain ⟨-, h'⟩ := by simpa using hl'
--       assumption
--     rw [last_eq_vx_getLast] at hx₁
--     apply aux (by simp) h₁.nodup hx₁

-- @[simp] lemma cons_isWalkFrom : G.IsWalkFrom S T (cons x e w) ↔
--     G.IsWalk w ∧ G.Inc₂ e x w.first ∧ x ∈ S ∧ w.last ∈ T := by
--   refine ⟨fun ⟨h, hS, hT⟩ ↦ ⟨?_, ?_, ?_, ?_⟩, fun ⟨hV, hS, hVd, hT⟩ ↦ ⟨?_, ?_, ?_⟩⟩
--   <;> simp_all only [cons_isWalk, first_cons, last_cons, and_self]


  -- induction w with
  -- | nil x => simp [reverse, hVd]
  -- | cons x e w ih =>
  --   simp only [cons_isWalk, reverse_cons] at hVd ⊢
  --   refine ValidIn.concat (ih hVd.2) ?_
  --   simp [hVd.1.symm]



@[simp]
lemma reverse_isWalk_iff : G.IsWalk w.reverse ↔ G.IsWalk w :=
  ⟨fun h ↦ by simpa using h.reverse, IsWalk.reverse⟩


lemma IsWalk.dedup [DecidableEq α] (h : G.IsWalk w) : G.IsWalk w.dedup :=
  h.sublist w.dedup_isSublist

lemma IsWalk.dropLast (h : G.IsWalk w) : G.IsWalk w.dropLast :=
  h.prefix <| w.dropLast_isPrefix


-- lemma _root_.Graph.IsPath.IsSuffix (hPf : w₁.IsSuffix w) (hP : G.IsPath w) : G.IsPath w₁ := by
--   simpa using hP.reverse.IsPrefix <| reverse_isPrefix_reverse_iff.2 hPf

end Graph

-- namespace WList

-- /-- Turn `w : WList α β` into a `Graph α β`. If the list is not well-formed
-- (i.e. it contains an edge appearing twice with different ends),
-- then the first occurence of the edge determines its ends in `w.toGraph`. -/
-- protected def toGraph : WList α β → Graph α β
--   | nil u => Graph.noEdge {u} β
--   | cons u e w => w.toGraph ∪ (Graph.singleEdge u w.first e)

-- @[simp]
-- lemma toGraph_nil : (WList.nil u (β := β)).toGraph = Graph.noEdge {u} β := rfl

-- @[simp]
-- lemma toGraph_cons : (w.cons u e).toGraph = w.toGraph ∪ (Graph.singleEdge u w.first e) := rfl

-- @[simp]
-- lemma toGraph_vxSet (w : WList α β) : w.toGraph.V = w.vxSet := by
--   induction w with simp_all

-- @[simp]
-- lemma toGraph_edgeSet (w : WList α β) : w.toGraph.E = w.edgeSet := by
--   induction w with simp_all

-- lemma toGraph_vxSet_nonempty (w : WList α β) : w.toGraph.V.Nonempty := by
--   simp

-- lemma WellFormed.toGraph_inc₂ (h : w.WellFormed) : w.toGraph.Inc₂ = w.Inc₂ := by
--   ext e x y
--   induction w with
--   | nil => simp
--   | cons u f w ih =>
--     rw [cons_wellFormed_iff] at h
--     rw [toGraph_cons, union_inc₂_iff, inc₂_cons_iff, ih h.1, toGraph_edgeSet, mem_edgeSet_iff,
--       singleEdge_inc₂_iff, eq_comm (a := e), iff_def, or_imp, and_iff_right (by tauto), or_imp,
--       and_iff_left (by tauto)]
--     rintro ⟨rfl, h_eq⟩
--     rw [and_iff_right rfl, and_iff_left h_eq, ← imp_iff_or_not]
--     intro hf
--     obtain ⟨y₁, y₂, hinc⟩ := exists_inc₂_of_mem_edge hf
--     rw [← h.2 y₁ y₂ hinc] at h_eq
--     obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := Sym2.eq_iff.1 h_eq
--     · assumption
--     exact hinc.symm

-- lemma Graph.IsWalk.toGraph_le (h : G.IsWalk w) : w.toGraph ≤ G := by
--   induction w with
--   | nil u => simpa [WList.toGraph] using h
--   | cons u e W ih =>
--     simp only [cons_isWalk_iff] at h
--     exact union_le (ih h.2) (by simpa using h.1)

-- lemma WellFormed.isWalk_toGraph (hw : w.WellFormed) : w.toGraph.IsWalk w := by
--   induction w with
--   | nil => simp
--   | cons u e w ih =>
--     rw [cons_wellFormed_iff] at hw
--     refine ((ih hw.1).of_le (by simp)).cons ?_
--     suffices w.toGraph.Inc₂ e u w.first ∨ e ∉ w.edge by simpa [toGraph_cons, union_inc₂_iff]
--     rw [← imp_iff_or_not]
--     intro he
--     obtain ⟨y₁, y₂, h⟩ := exists_inc₂_of_mem_edge he
--     rw [((ih hw.1).inc₂_of_inc₂ h).inc₂_iff_sym2_eq, hw.2 _ _ h]




-- end WList
