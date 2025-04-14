import Kura.Walk.Defs


namespace Graph
open Set Function List Nat Walk
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ : Walk α β}
namespace Walk


def concat : Walk α β → β → α → Walk α β
| nil x, e, y => cons x e (nil y)
| cons x e w, f, y => cons x e (w.concat f y)

def dropLast : Walk α β → Walk α β
| nil x => nil x
| cons x _ (nil _) => nil x
| cons x e (cons y e' w) => cons x e ((cons y e' w).dropLast)

def append : Walk α β → Walk α β → Walk α β
| nil _x, w => w
| cons x e w, w' => cons x e (w.append w')

instance instAppend : Append (Walk α β) where
  append := append

def IsPrefix : Walk α β → Walk α β → Prop :=
  fun W w => ∃ w', W = w ++ w' ∧ w.last = w'.first

def IsSuffix : Walk α β → Walk α β → Prop :=
  fun W w => ∃ w', W = w' ++ w ∧ w'.last = w.first

def reverse : Walk α β → Walk α β
| nil x => nil x
| cons x e w => w.reverse.concat e x


/-- Properties of dropLast operation -/
@[simp]
lemma dropLast_nil : (nil x : Walk α β).dropLast = nil x := rfl

@[simp]
lemma dropLast_cons_nil : (cons x e (nil y) : Walk α β).dropLast = nil x := rfl

@[simp]
lemma dropLast_cons_cons :
  (cons x e (cons y e' w) : Walk α β).dropLast = cons x e ((cons y e' w).dropLast) := rfl

@[simp]
lemma dropLast_first {w : Walk α β} (h : w.Nonempty) : (w.dropLast).first = w.first := by
  match w with
  | .nil x => simp at h
  | .cons x e (.nil y) => simp
  | .cons x e (cons y e' w) => simp

@[simp]
lemma dropLast_vx {w : Walk α β} (h : w.Nonempty) : (w.dropLast).vx = w.vx.dropLast := by
  match w with
  | .nil x => simp only [Nonempty.not_nil] at h
  | .cons x e (.nil y) => simp only [dropLast, nil_vx, cons_vx, dropLast_cons₂, dropLast_single]
  | .cons x e (cons y e' w) =>
    simp only [dropLast, cons_vx, dropLast_cons₂, List.cons.injEq, true_and]
    rw [← cons_vx (e := e')]
    apply dropLast_vx (by simp)

@[simp]
lemma dropLast_edge {w : Walk α β} (h : w.Nonempty) : (w.dropLast).edge = w.edge.dropLast := by
  match w with
  | .nil x => simp only [Nonempty.not_nil] at h
  | .cons x e (.nil y) => simp only [dropLast, nil_edge, cons_edge, dropLast_single]
  | .cons x e (cons y e' w) =>
    simp only [dropLast, cons_edge, dropLast_cons₂, List.cons.injEq, true_and]
    exact dropLast_edge (by simp)

lemma dropLast_validIn {w : Walk α β} (hVd : w.ValidIn G) : (w.dropLast).ValidIn G := by
  match w with
  | .nil x => simp only [dropLast, hVd]
  | .cons x e (.nil y) =>
    simp only [cons_validIn, nil_first, nil_validIn] at hVd
    exact hVd.1.vx_mem_left
  | .cons x e (cons y e' w) =>
    rw [dropLast, cons_validIn, dropLast_first (by simp)]
    rw [cons_validIn] at hVd
    exact ⟨hVd.1, dropLast_validIn hVd.2⟩

lemma mem_dropLast_or_last_of_mem {w : Walk α β} (hu : u ∈ w) : u ∈ w.dropLast ∨ u = w.last := by
  match w with
  | .nil x => simpa using hu
  | .cons x e (.nil y) =>
    simp only [mem_cons_iff, mem_nil_iff] at hu
    obtain rfl | rfl := hu <;> simp
  | .cons x e (cons y e' w) =>
    simp only [mem_cons_iff] at hu
    obtain rfl | rfl | hu := hu
    · simp
    · simp only [dropLast_cons_cons, mem_cons_iff, cons_last]
      have := mem_dropLast_or_last_of_mem (by simp : u ∈ (cons u e' w))
      rw [cons_last] at this
      tauto
    · simp only [dropLast_cons_cons, mem_cons_iff, cons_last]
      have := mem_dropLast_or_last_of_mem (by simp [hu] : u ∈ (cons y e' w))
      rw [cons_last] at this
      tauto

lemma mem_of_mem_dropLast {w : Walk α β} (h : u ∈ w.dropLast) : u ∈ w := by
  match w with
  | .nil x => simpa using h
  | .cons x e (.nil y) => simp_all only [dropLast_cons_nil, mem_nil_iff, mem_cons_iff, true_or]
  | .cons x e (cons y e' w) =>
    simp only [dropLast_cons_cons, mem_cons_iff] at h ⊢
    obtain rfl | h := h
    · left
      rfl
    · have := mem_of_mem_dropLast (w := cons y e' w) (by simpa only [Nonempty.cons_true,
      dropLast_vx, cons_vx])
      right
      simpa only [mem_cons_iff] using this

lemma mem_dropLast_or_last_of_mem_iff :
    u ∈ w.dropLast ∨ u = w.last ↔ u ∈ w := by
  refine ⟨?_, mem_dropLast_or_last_of_mem⟩
  rintro (h | rfl)
  · exact mem_of_mem_dropLast h
  · exact last_mem

@[simp]
lemma dropLast_vxSet_of_isPath {w : Walk α β} (hP : G.IsPath w) (hn : w.Nonempty) :
    (w.dropLast).vxSet = w.vxSet \ {w.last} := by
  match w with
  | .nil x => simp at hn
  | .cons x e (.nil y) =>
    simp only [dropLast_cons_nil, nil_vxSet, cons_vxSet, union_singleton, cons_last, nil_last,
      mem_singleton_iff, insert_diff_of_mem]
    rw [diff_singleton_eq_self]
    simp only [mem_singleton_iff]
    rintro rfl
    simp at hP
  | .cons x e (cons y e' w) =>
    have := dropLast_vxSet_of_isPath (w := cons y e' w)
    simp only [cons_isPath, Nonempty.cons_true, cons_vxSet, singleton_union, cons_last,
      forall_const, and_imp, cons_first, mem_cons_iff, not_or, dropLast_cons_cons,
      union_insert] at this hP ⊢
    obtain ⟨⟨hP, h₂', hynin⟩, h₂, hne, hxnin⟩ := hP
    rw [this hP h₂' hynin, ← insert_diff_of_not_mem, insert_comm]
    simp only [mem_singleton_iff]
    rintro rfl
    simp only [last_mem, not_true_eq_false] at hxnin

@[simp]
lemma last_not_mem_dropLast_of_isPath {w : Walk α β} (hP : G.IsPath w) (hn : w.Nonempty) :
    w.last ∉ w.dropLast := by
  rintro h
  rw [← mem_vxSet_iff, dropLast_vxSet_of_isPath hP hn] at h
  simp at h

/-- Properties of concat operation -/
@[simp]
lemma nil_concat : (nil x).concat e y = cons x e (nil y) := rfl

@[simp]
lemma cons_concat : (cons x e w).concat f y = cons x e (w.concat f y) := rfl

@[simp]
lemma concat_first : (w.concat e v).first = w.first := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_last : (w.concat e v).last = v := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_vx : (w.concat e v).vx = w.vx ++ [v] := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_edge : (w.concat e v).edge = w.edge ++ [e] := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_length : (w.concat e v).length = w.length + 1 := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

lemma ValidIn.concat (hVd : w.ValidIn G) (h₂ : G.Inc₂ e w.last v) : (w.concat e v).ValidIn G := by
  induction w with
  | nil x =>
    simp only [nil_validIn, nil_last] at hVd h₂
    simp [concat, hVd, h₂, h₂.vx_mem_right]
  | cons x e' w' ih =>
    simp only [cons_validIn, cons_last, cons_concat, concat_first] at hVd h₂ ⊢
    exact ⟨hVd.1, ih hVd.2 h₂⟩

/-- Properties of reverse operation -/
@[simp]
lemma reverse_nil : (nil x : Walk α β).reverse = nil x := rfl

@[simp]
lemma reverse_cons : (cons x e w).reverse = (w.reverse).concat e x := rfl

@[simp]
lemma reverse_first : (reverse w).first = w.last := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_last : (reverse w).last = w.first := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_vx : (reverse w).vx = w.vx.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_edge {w : Walk α β} : (reverse w).edge = w.edge.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_length {w : Walk α β} : (reverse w).length = w.length := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

lemma ValidIn.reverse (hVd : w.ValidIn G) : (reverse w).ValidIn G := by
  induction w with
  | nil x => simp [reverse, hVd]
  | cons x e w ih =>
    simp only [cons_validIn, reverse_cons] at hVd ⊢
    refine ValidIn.concat (ih hVd.2) ?_
    simp [hVd.1.symm]

lemma IsWalkFrom.reverse (h : G.IsWalkFrom S T w) : G.IsWalkFrom T S w.reverse where
  validIn := h.validIn.reverse
  first_mem := by simp [h.last_mem]
  last_mem := by simp [h.first_mem]

lemma IsPath.reverse (hp : G.IsPath w) : G.IsPath w.reverse where
  validIn := hp.validIn.reverse
  nodup := by simp [hp.nodup]

lemma IsPathFrom.reverse (p : G.IsPathFrom S T w) : G.IsPathFrom T S w.reverse where
  validIn := p.validIn.reverse
  nodup := by simp [p.nodup]
  first_mem := by simp [p.last_mem]
  last_mem := by simp [p.first_mem]

/- Properties of append operation -/
@[simp]
lemma append_notation : append w₁ w₂ = w₁ ++ w₂ := rfl

@[simp]
lemma nil_append : nil x ++ w₂ = w₂ := by
  simp only [← append_notation, append]

@[simp]
lemma cons_append : cons x e w₁ ++ w₂ = cons x e (w₁ ++ w₂) := by
  simp only [← append_notation, append]

@[simp]
lemma append_vx : (w₁ ++ w₂).vx = w₁.vx.dropLast ++ w₂.vx := by
  induction w₁ with
  | nil x => simp
  | cons x e w ih =>
    simp only [append_notation, append, cons_vx]
    rw [List.dropLast_cons_of_ne_nil vx_ne_nil, List.cons_append]
    simpa

lemma append_vx' {w₁ w₂ : Walk α β} (heq : w₁.last = w₂.first) :
    (w₁ ++ w₂).vx = w₁.vx ++ w₂.vx.tail := by
  match w₁ with
  | .nil x =>
    simp_all only [nil_last, append_vx, nil_vx, dropLast_single, nil_append, cons_append]
    rw [first_eq_vx_head]
    exact (head_cons_tail w₂.vx vx_ne_nil).symm
  | .cons x e w =>
    simp only [cons_last, cons_append, cons_vx, List.cons_append, List.cons.injEq,
      true_and] at heq ⊢
    exact append_vx' heq

@[simp]
lemma append_edge {w₁ w₂ : Walk α β} : (w₁ ++ w₂).edge = w₁.edge ++ w₂.edge := by
  induction w₁ with
  | nil x => simp only [nil_append, nil_edge, List.nil_append]
  | cons x e w ih => simp only [cons_append, cons_edge, ih, List.cons_append]

@[simp]
lemma append_length : (w₁ ++ w₂).length = w₁.length + w₂.length := by
  induction w₁ with
  | nil x => simp only [nil_append, nil_length, zero_add]
  | cons x e w ih =>
    simp only [cons_append, cons_length, ih]
    omega

@[simp]
lemma append_nil (h : w.last = x) : w ++ (nil x) = w := by
  induction w with
  | nil u => aesop
  | cons u e W ih =>
    rw [cons_last] at h
    rw [cons_append, ih h]

@[simp]
lemma append_first_of_eq (h : w₁.last = w₂.first):
  (w₁ ++ w₂).first = w₁.first := by
  induction w₁ with
  | nil x => simp only [nil_append, ← h, nil_last, nil_first]
  | cons x e w ih => simp only [cons_append, cons_first]

@[simp]
lemma append_first_of_nonempty (h : w₁.Nonempty) :
  (w₁ ++ w₂).first = w₁.first := by
  induction w₁ with
  | nil x => simp only [Nonempty.not_nil] at h
  | cons x e w ih => simp only [cons_append, cons_first]

@[simp]
lemma append_last :
  (w₁ ++ w₂).last = w₂.last := by
  induction w₁ with
  | nil x => simp only [nil_append]
  | cons x e w ih => simp only [cons_append, cons_last, ih]

lemma append_assoc (w1 w2 w3 : Walk α β) : (w1 ++ w2) ++ w3 = w1 ++ (w2 ++ w3) := by
  induction w1 with
  | nil x => simp only [nil_append]
  | cons x e w ih => simp only [cons_append, ih]

lemma append_right_injective : Injective (w ++ ·) := by
  rintro w₁ w₂ h
  induction w with
  | nil x => simpa only [nil_append] using h
  | cons x e w ih =>
    simp only [cons_append, cons.injEq, true_and] at h
    exact ih h

@[simp]
lemma append_right_inj : w ++ w₁ = w ++ w₂ ↔ w₁ = w₂ := by
  constructor
  · apply append_right_injective
  · rintro rfl
    rfl

@[simp]
lemma append_right_eq_self : w ++ w₁ = w ↔ w₁ = nil w.last := by
  induction w with
  | nil x => simp only [nil_append, nil_last]
  | cons x e w ih => simpa only [cons_append, cons.injEq, true_and, cons_last]

@[simp]
lemma append_left_eq_self : w₁ ++ w = w ↔ ¬ w₁.Nonempty := by
  induction w₁ with
  | nil x => simp only [nil_append, Nonempty.not_nil, not_false_eq_true]
  | cons x e w ih =>
    simp only [cons_append, Nonempty.cons_true, not_true_eq_false, iff_false]
    intro hcons
    apply_fun length at hcons
    simp only [cons_length, append_length] at hcons
    omega

@[simp]
lemma append_eq_nil_iff : w₁ ++ w₂ = nil x ↔ (∃ y, w₁ = nil y) ∧ w₂ = nil x := by
  induction w₁ with
  | nil y => simp only [nil_append, nil.injEq, exists_eq', true_and]
  | cons y e w ih => simp only [cons_append, reduceCtorEq, exists_false, false_and]

lemma append_validIn (h : w₁.last = w₂.first) (h₁ : w₁.ValidIn G) (h₂ : w₂.ValidIn G) :
  (w₁ ++ w₂).ValidIn G := by
  induction w₁ with
  | nil x => simpa
  | cons x e w₁ ih =>
    simp only [cons_last] at h
    refine ⟨?_, by simp [ih h h₁.2]⟩
    convert h₁.1 using 1
    exact append_first_of_eq h

lemma ValidIn.append_left_validIn {w₁ w₂ : Walk α β} (h : w₁.last = w₂.first)
    (hVd : (w₁ ++ w₂).ValidIn G) : w₁.ValidIn G := by
  match w₁ with
  | .nil x =>
    simp only [nil_last, nil_append, nil_validIn] at h hVd ⊢
    subst x
    exact hVd.vx_mem_of_mem first_mem
  | .cons x e w =>
    simp only [cons_last] at h
    simp only [cons_append, cons_validIn] at hVd
    refine ⟨?_, ValidIn.append_left_validIn h hVd.2⟩
    convert hVd.1 using 1
    exact (append_first_of_eq h).symm

lemma ValidIn.append_right_validIn (hVd : (w₁ ++ w₂).ValidIn G) : w₂.ValidIn G := by
  induction w₁ with
  | nil x => simpa only [nil_append] using hVd
  | cons x e w ih =>
    simp only [cons_append, cons_validIn] at hVd
    exact ih hVd.2

lemma ValidIn.last_eq_first (hw₁ : w₁.Nonempty) (hVd₁ : w₁.ValidIn G) (hVd : (w₁ ++ w₂).ValidIn G) :
  w₁.last = w₂.first := by
  induction w₁ with
  | nil x => simp only [Nonempty.not_nil] at hw₁
  | cons x e w ih =>
    simp_all only [Nonempty.cons_true, cons_append, cons_validIn, cons_last, forall_const]
    by_cases hNonempty : w.Nonempty
    · simp_all only [forall_const, append_first_of_eq, true_and]
    · simp only [Nonempty.not_iff] at hNonempty
      obtain ⟨y, rfl⟩ := hNonempty
      simp_all only [Nonempty.not_nil, nil_last, IsEmpty.forall_iff, nil_first, nil_validIn,
        nil_append]
      exact hVd₁.1.eq_of_inc₂ hVd.1

lemma append_isWalkFrom (h : w₁.last = w₂.first) (h₁ : G.IsWalkFrom S T w₁)
    (h₂ : G.IsWalkFrom T U w₂) : G.IsWalkFrom S U (w₁ ++ w₂) := by
  obtain ⟨hw₁Vd, hw₁first, hw₁last⟩ := h₁
  obtain ⟨hw₂Vd, hw₂first, hw₂last⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · exact Walk.append_validIn h hw₁Vd hw₂Vd
  · simpa [h]
  · simpa

lemma append_isPath (h : w₁.last = w₂.first) (h₁ : G.IsPath w₁) (h₂ : G.IsPath w₂)
    (hvxSet : w₁.vxSet ∩ w₂.vxSet ⊆ {w₁.last}) : G.IsPath (w₁ ++ w₂) where
  validIn := append_validIn h h₁.validIn h₂.validIn
  nodup := by
    simp only [Set.subset_singleton_iff, Set.mem_inter_iff, mem_vxSet_iff, and_imp, append_vx,
      nodup_append, h₁.nodup.dropLast, h₂.nodup, true_and] at hvxSet ⊢
    rintro x hx₁ hx₂
    obtain rfl := hvxSet x (List.mem_of_mem_dropLast hx₁) hx₂
    by_cases h : w₁.Nonempty
    · rw [last_eq_vx_getLast] at hx₁
      simp only [getLast_not_mem_dropLast_of_nodup h₁.nodup] at hx₁
    · rw [Nonempty.not_iff] at h
      obtain ⟨y, rfl⟩ := h
      rw [nil_last] at h
      subst y
      simp at hx₁

lemma append_left_isPath (h : w₁.last = w₂.first) (hP : G.IsPath (w₁ ++ w₂)) : G.IsPath w₁ where
  validIn := hP.validIn.append_left_validIn h
  nodup := by
    have := hP.nodup
    rw [append_vx' h] at this
    exact this.of_append_left

lemma append_right_isPath (hP : G.IsPath (w₁ ++ w₂)) : G.IsPath w₂ where
  validIn := hP.validIn.append_right_validIn
  nodup := by
    have := hP.nodup
    rw [append_vx] at this
    exact this.of_append_right

lemma not_mem_prefix_of_mem_suffix_tail (heq : w₁.last = w₂.first) (hP : G.IsPath (w₁ ++ w₂))
    (hmem : u ∈ w₂.vx.tail) : u ∉ w₁.vx := by
  have := hP.nodup
  rw [append_vx' heq, nodup_append] at this
  exact (this.2.2 · hmem)

lemma not_mem_suffix_of_mem_prefix_dropLast (hP : G.IsPath (w₁ ++ w₂)) (hmem : u ∈ w₁.vx.dropLast) :
    u ∉ w₂.vx := by
  have := hP.nodup
  rw [append_vx, nodup_append] at this
  exact this.2.2 hmem

lemma eq_first_of_mem_prefix_suffix (hP : G.IsPath (w₁ ++ w₂)) (heq : w₁.last = w₂.first)
    (hmem1 : u ∈ w₁.vx) (hmem2 : u ∈ w₂.vx) : u = w₂.first := by
  have := hP.nodup
  rw [append_vx' heq, nodup_append] at this
  have := this.2.2 hmem1
  rw [← w₂.vx.head_cons_tail vx_ne_nil, mem_cons, ← first_eq_vx_head] at hmem2
  simp_all only [imp_false, or_false]

lemma eq_last_of_mem_prefix_suffix (hP : G.IsPath (w₁ ++ w₂)) (heq : w₁.last = w₂.first)
    (hmem1 : u ∈ w₁.vx) (hmem2 : u ∈ w₂.vx) : u = w₁.last :=
  heq ▸ eq_first_of_mem_prefix_suffix hP heq hmem1 hmem2

lemma eq_append_of_vx_mem {w : Walk α β} {u : α} (hmem : u ∈ w) :
    ∃ w₁ w₂ : Walk α β, w = w₁ ++ w₂ ∧ w₁.last = u ∧ w₂.first = u := by
  induction w with
  | nil x =>
    rw [mem_nil_iff] at hmem
    subst u
    exact ⟨nil x, nil x, rfl, rfl, rfl⟩
  | cons x e w ih =>
    rw [mem_cons_iff] at hmem
    obtain rfl | h := hmem
    · exact ⟨nil u, cons u e w, rfl, rfl, rfl⟩
    · obtain ⟨w₁, w₂, rfl, hfin, hfirst⟩ := ih h
      use cons x e w₁, w₂
      simp only [cons_append, cons_last, hfin, hfirst, and_self]

lemma eq_append_cons_of_edge_mem {w : Walk α β} {e : β} (he : e ∈ w.edge) :
    ∃ w₁ w₂ : Walk α β, w = w₁ ++ cons w₁.last e w₂ ∧ e ∉ w₁.edge := by
  induction w with
  | nil x => simp only [nil_edge, not_mem_nil] at he
  | cons x e' w ih =>
    simp only [cons_edge, mem_cons] at he
    obtain rfl | he' := he
    · use nil x, w, rfl, by simp only [nil_edge, not_mem_nil, not_false_eq_true]
    · by_cases h : e = e'
      · subst e'
        use nil x, w, rfl, by simp only [nil_edge, not_mem_nil, not_false_eq_true]
      · obtain ⟨w₁, w₂, rfl, hnin⟩ := ih he'
        use cons x e' w₁, w₂, by simp only [cons_last, cons_append]
        simp only [cons_edge, mem_cons, h, hnin, or_self, not_false_eq_true]

/- Properties of IsPrefix -/
namespace IsPrefix

instance instIsPrefixPreorder: IsPreorder (Walk α β) IsPrefix where
  refl w := ⟨nil w.last, by simp [append_nil rfl]⟩
  trans w1 w2 w3 h12 h23 := by
    obtain ⟨w12, rfl, heq1⟩ := h12
    obtain ⟨w23, rfl, heq2⟩ := h23
    use w23 ++ w12
    rw [← append_assoc, heq2]
    rw [append_last] at heq1
    simp only [heq1, append_first_of_eq, and_self]

lemma ValidIn.IsPrefix (hPf : w.IsPrefix w₁) (hVd : w.ValidIn G) : w₁.ValidIn G := by
  obtain ⟨w₂, rfl, heq⟩ := hPf
  exact hVd.append_left_validIn heq

lemma IsPath.IsPrefix (hPf : w.IsPrefix w₁) (hP : G.IsPath w) : G.IsPath w₁ := by
  obtain ⟨w₂, rfl, heq⟩ := hPf
  exact append_left_isPath heq hP

end IsPrefix

namespace IsSuffix

instance instIsSuffixPartialOrder: IsPartialOrder (Walk α β) IsSuffix where
  refl w := ⟨nil w.first, by simp [append_nil rfl]⟩
  trans w1 w2 w3 h12 h23 := by
    obtain ⟨w12, rfl, heq1⟩ := h12
    obtain ⟨w23, rfl, heq2⟩ := h23
    simp only [heq2, append_first_of_eq] at heq1
    use w12 ++ w23
    rw [← append_assoc]
    simpa
  antisymm w1 w2 h12 h21 := by
    obtain ⟨w21, hw21, heq21⟩ := h21
    obtain ⟨w12, hw12, heq12⟩ := h12
    have := hw12 ▸ hw21 ▸ hw12
    rw [append_right_inj, ← append_assoc, eq_comm, append_left_eq_self] at this
    simp only [Nonempty.not_iff, append_eq_nil_iff, exists_and_left] at this
    obtain ⟨⟨y, rfl⟩, x, rfl⟩ := this
    simpa using hw12

lemma ValidIn.IsSuffix (hPf : w.IsSuffix w₁) (hVd : w.ValidIn G) : w₁.ValidIn G := by
  obtain ⟨w₂, rfl, heq⟩ := hPf
  exact hVd.append_right_validIn

lemma IsPath.IsSuffix (hPf : w.IsSuffix w₁) (hP : G.IsPath w) : G.IsPath w₁ := by
  obtain ⟨w₂, rfl, heq⟩ := hPf
  exact append_right_isPath hP

end IsSuffix

lemma Connected.exist_walk (h : G.Connected u v) : ∃ (W : Walk α β), W.ValidIn G ∧
    W.first = u ∧ W.last = v := by
  induction h with
  | single hradj =>
    obtain ⟨W, hW, hlength, hfirst, hlast⟩ := hradj.exist_walk
    use W
  | tail hconn hradj ih =>
    expose_names
    obtain ⟨W, hW, hfirst, hlast⟩ := ih
    obtain ⟨W', hW', hlength, hfirst', hlast'⟩ := hradj.exist_walk
    subst b c u
    use W ++ W', append_validIn hfirst'.symm hW hW'
    simp only [hfirst', append_first_of_eq, append_last, and_self]

theorem Connected.iff_walk : G.Connected u v ↔ ∃ w : Walk α β, w.ValidIn G ∧ w.first = u ∧ w.last = v := by
  constructor
  · exact fun a ↦ exist_walk a
  · rintro ⟨w, h1, rfl, rfl⟩
    exact h1.connected

end Walk
