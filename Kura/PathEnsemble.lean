import Kura.Walk

open Set Function List Nat
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β}
namespace Graph
namespace Path

open Walk

structure PathEnsemble (α β : Type*) where
  Paths : Set (Path α β)
  Disj : Disjoint Paths

namespace PathEnsemble

def Empty (α β : Type*) : PathEnsemble α β where
  Paths := ∅
  Disj := by
    rintro x p q hp hq hxp hxq
    exact False.elim hp

def nil (U : Set α) (β : Type*) : PathEnsemble α β where
  Paths := Path.nil '' U
  Disj := by
    rintro x p q hp hq hxp hxq
    simp only [mem_image] at hp hq
    obtain ⟨u, hu, rfl⟩ := hp
    obtain ⟨v, hv, rfl⟩ := hq
    simp only [vx, Graph.Path.nil, nil_vx, mem_cons, not_mem_nil, or_false] at hxp hxq
    subst u v
    rfl

def ValidOn (Ps : PathEnsemble α β) (G : Graph α β) := ∀ p ∈ Ps.Paths, p.val.ValidOn G

def StartSet (Ps : PathEnsemble α β) : Set α := (·.val.start) '' Ps.Paths

def FinishSet (Ps : PathEnsemble α β) : Set α := (·.val.finish) '' Ps.Paths

def VxSet (Ps : PathEnsemble α β) : Set α := {x | ∃ p ∈ Ps.Paths, x ∈ p.val.vx}

def EdgeSet (Ps : PathEnsemble α β) : Set β := {e | ∃ p ∈ Ps.Paths, e ∈ p.val.edge}

def InternalVsSet (Ps : PathEnsemble α β) : Set α := {x | ∃ p ∈ Ps.Paths, x ∈ p.val.vx.tail.dropLast}

def insert (p : Path α β) (Ps : PathEnsemble α β) (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) : PathEnsemble α β where
  Paths := Ps.Paths ∪ {p}
  Disj := by
    rintro x p₁ p₂ hp1 hp2 hxp hxq
    simp only [union_singleton, Set.mem_insert_iff] at hp1 hp2
    simp only [VxSet, mem_setOf_eq, not_exists, not_and] at h
    obtain (rfl | h1) := hp1 <;> obtain (rfl | h2) := hp2
    · rfl
    · exact (h x hxp p₂ h2 hxq).elim
    · exact (h x hxq p₁ h1 hxp).elim
    · exact Ps.Disj x p₁ p₂ h1 h2 hxp hxq

lemma start_injOn (Ps : PathEnsemble α β) : InjOn (·.val.start) Ps.Paths := by
  rintro p₁ hp₁ p₂ hp₂ hstart
  exact Ps.Disj _ _ _ hp₁ hp₂ start_vx_mem (by
    beta_reduce at hstart
    exact hstart ▸ start_vx_mem)

lemma finish_injOn (Ps : PathEnsemble α β) : InjOn (·.val.finish) Ps.Paths := by
  rintro p₁ hp₁ p₂ hp₂ hfinish
  exact Ps.Disj _ _ _ hp₁ hp₂ finish_vx_mem (by
    beta_reduce at hfinish
    exact hfinish ▸ finish_vx_mem)

lemma unique_path_start (Ps : PathEnsemble α β)  :
    ∀ x ∈ Ps.StartSet, ∃! p ∈ Ps.Paths, p.val.start = x := by
  rintro x ⟨p, hp, rfl⟩
  use p, ⟨hp, rfl⟩, (fun q hq ↦ start_injOn Ps hq.1 hp hq.2)

lemma unique_path_finish (Ps : PathEnsemble α β) :
    ∀ x ∈ Ps.FinishSet, ∃! p ∈ Ps.Paths, p.val.finish = x := by
  rintro x ⟨p, hp, rfl⟩
  use p, ⟨hp, rfl⟩, (fun q hq ↦ finish_injOn Ps hq.1 hp hq.2)

noncomputable def byStart (Ps : PathEnsemble α β) (u : α) (hu : u ∈ Ps.StartSet) : Path α β :=
  (Ps.unique_path_start u hu).choose

noncomputable def byFinish (Ps : PathEnsemble α β) (u : α) (hu : u ∈ Ps.FinishSet) : Path α β :=
  (Ps.unique_path_finish u hu).choose

variable {Ps : PathEnsemble α β} {u : α}

@[simp]
lemma byStart_mem (hu : u ∈ Ps.StartSet) :
    Ps.byStart u hu ∈ Ps.Paths := (Ps.unique_path_start u hu).choose_spec.1.1

@[simp]
lemma byFinish_mem (hu : u ∈ Ps.FinishSet) :
    Ps.byFinish u hu ∈ Ps.Paths := (Ps.unique_path_finish u hu).choose_spec.1.1

@[simp]
lemma byStart_start (hu : u ∈ Ps.StartSet) :
    (Ps.byStart u hu).val.start = u := (Ps.unique_path_start u hu).choose_spec.1.2

@[simp]
lemma byFinish_finish (hu : u ∈ Ps.FinishSet) :
    (Ps.byFinish u hu).val.finish = u := (Ps.unique_path_finish u hu).choose_spec.1.2

lemma byStart_injective (Ps : PathEnsemble α β) :
    Injective (fun a ↦ Ps.byStart a.val a.prop : Ps.StartSet → Path α β) := by
  rintro x y h
  beta_reduce at h
  rw [Subtype.ext_iff, ← byStart_start x.prop, h, byStart_start y.prop]

lemma byFinish_injective (Ps : PathEnsemble α β) :
    Injective (fun a ↦ Ps.byFinish a.val a.prop : Ps.FinishSet → Path α β) := by
  rintro x y h
  beta_reduce at h
  rw [Subtype.ext_iff, ← byFinish_finish x.prop, h, byFinish_finish y.prop]

variable {Ps Ps₁ Ps₂ : PathEnsemble α β} {u v x y : α} {p q : Path α β} {U S T : Set α}

@[simp]
lemma byStart_inj (hu : u ∈ Ps.StartSet) (hv : v ∈ Ps.StartSet) :
    Ps.byStart u hu = Ps.byStart v hv ↔ u = v := by
  change (fun a ↦ Ps.byStart a.val a.prop : Ps.StartSet → Path α β) ⟨u, hu⟩ = (fun a ↦ Ps.byStart a.val a.prop : Ps.StartSet → Path α β) ⟨v, hv⟩ ↔ u = v
  rw [byStart_injective Ps |>.eq_iff, Subtype.ext_iff]

@[simp]
lemma byFinish_inj (hu : u ∈ Ps.FinishSet) (hv : v ∈ Ps.FinishSet) :
    Ps.byFinish u hu = Ps.byFinish v hv ↔ u = v := by
  change (fun a ↦ Ps.byFinish a.val a.prop : Ps.FinishSet → Path α β) ⟨u, hu⟩ = (fun a ↦ Ps.byFinish a.val a.prop : Ps.FinishSet → Path α β) ⟨v, hv⟩ ↔ u = v
  rw [byFinish_injective Ps |>.eq_iff, Subtype.ext_iff]

lemma mem_finishSet_mem (hu : u ∈ Ps.FinishSet) (hup : u ∈ p.val.vx) (hp : p ∈ Ps.Paths) :
    u = p.val.finish := by
  obtain ⟨q, hq, rfl⟩ := hu
  rw [Ps.Disj q.val.finish q p hq hp finish_vx_mem hup]

lemma mem_startSet_mem (hv : v ∈ Ps.StartSet) (hvp : v ∈ p.val.vx) (hp : p ∈ Ps.Paths) :
    v = p.val.start := by
  obtain ⟨q, hq, rfl⟩ := hv
  rw [Ps.Disj q.val.start q p hq hp start_vx_mem hvp]

@[simp]
lemma start_mem_StartSet (hp : p ∈ Ps.Paths) : p.val.start ∈ Ps.StartSet := by
  use p, hp

@[simp]
lemma finish_mem_FinishSet (hp : p ∈ Ps.Paths) : p.val.finish ∈ Ps.FinishSet := by
  use p, hp

@[simp]
lemma byStart_of_start (hp : p ∈ Ps.Paths) : Ps.byStart p.val.start (start_mem_StartSet hp) = p :=
  ((Ps.unique_path_start p.val.start (start_mem_StartSet hp)).choose_spec.2 p ⟨hp, rfl⟩).symm

@[simp]
lemma byFinish_of_finish (hp : p ∈ Ps.Paths) : Ps.byFinish p.val.finish (finish_mem_FinishSet hp) = p :=
  ((Ps.unique_path_finish p.val.finish (finish_mem_FinishSet hp)).choose_spec.2 p ⟨hp, rfl⟩).symm

lemma append_aux {Ps₁ Ps₂ : PathEnsemble α β} (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (hu : u ∈ Ps₁.FinishSet) (hv : v ∈ Ps₂.StartSet)
    (hx1 : x ∈ (Ps₁.byFinish u hu).val.vx.dropLast) (hx2 : x ∈ (Ps₂.byStart v hv).val.vx) :
    False := by
  have hx1' : x ∈ Ps₁.VxSet := by
    use Ps₁.byFinish u hu, byFinish_mem hu, List.mem_of_mem_dropLast hx1
  have hx2' : x ∈ Ps₂.VxSet := by
    use Ps₂.byStart v hv, byStart_mem hv, hx2
  have := mem_finishSet_mem (hsu ⟨hx1', hx2'⟩) (List.mem_of_mem_dropLast hx1) (byFinish_mem hu)
  exact finish_not_mem_vx_dropLast (this ▸ hx1)

def append (Ps₁ Ps₂ : PathEnsemble α β) (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) : PathEnsemble α β where
  Paths :=
    let f : ↑(Ps₁.FinishSet) → Path α β := fun ⟨a, ha⟩ ↦
      Ps₁.byFinish a ha|>.append (Ps₂.byStart a (heq ▸ ha)) fun b ↦ append_aux hsu ha (heq ▸ ha)
    Set.range f
  Disj x p q hp hq hxp hxq := by
    simp only [Set.mem_range, Subtype.exists] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    simp only [append_vx, mem_append] at hxp hxq
    obtain (hxp1 | hxp2) := hxp <;> obtain (hxq1 | hxq2) := hxq
    · have := Ps₁.Disj x _ _ (byFinish_mem ha) (byFinish_mem hb) (List.dropLast_subset _ hxp1) (List.dropLast_subset _ hxq1)
      rw [byFinish_inj] at this
      subst b
      rfl
    · exact (append_aux hsu ha (heq ▸ hb) hxp1 hxq2).elim
    · exact (append_aux hsu hb (heq ▸ ha) hxq1 hxp2).elim
    · have := Ps₂.Disj x _ _ (byStart_mem (heq ▸ ha)) (byStart_mem (heq ▸ hb)) hxp2 hxq2
      rw [byStart_inj] at this
      subst b
      rfl

-- def appendOnSep (Ps₁ Ps₂ : PathEnsemble α β) (heq : Ps₁.FinishSet = Ps₂.StartSet)
--     (hsep : G.IsVxSetSeparator Ps₁.FinishSet Ps₁.StartSet Ps₂.FinishSet) : PathEnsemble α β :=
--   Ps₁.append Ps₂ (by
--     rintro x ⟨⟨p, hp1, hxp⟩, q, hq2, hxq⟩


--     rw [h1Finish] at hx
--     exact hsep.1 hx) (by
--     rintro x hx
--     rw [h2Start] at hx
--     exact hsep.2 hx)

@[simp]
lemma Empty_validOn : (Empty α β).ValidOn G := by
  rintro p hp
  exact False.elim hp

@[simp]
lemma Empty_finite : (Empty α β).Paths.Finite := by
  simp only [Empty, finite_empty]

@[simp]
lemma Empty_ncard : (Empty α β).Paths.ncard = 0 := by
  simp only [Empty, ncard_empty]

@[simp]
lemma Empty_VxSet : (Empty α β).VxSet = ∅ := by
  simp only [VxSet, Empty, mem_empty_iff_false, false_and, exists_false, setOf_false]

@[simp]
lemma Empty_EdgeSet : (Empty α β).EdgeSet = ∅ := by
  simp only [EdgeSet, Empty, mem_empty_iff_false, false_and, exists_false, setOf_false]

@[simp]
lemma Empty_startSet : (Empty α β).StartSet = ∅ := by
  simp only [StartSet, Empty, image_empty]

@[simp]
lemma Empty_finishSet : (Empty α β).FinishSet = ∅ := by
  simp only [FinishSet, Empty, image_empty]

@[simp]
lemma nil_validOn : (nil U β).ValidOn (G[U]) := by
  rintro p ⟨x, hx, rfl⟩
  simpa only [Path.nil, nil_validOn_iff, induce_V]

@[simp]
lemma nil_validOn' (hUV : U ⊆ G.V) : (nil U β).ValidOn G := by
  rintro p ⟨x, hx, rfl⟩
  simp only [Path.nil, nil_validOn_iff]
  exact hUV hx

@[simp]
lemma mem_nil_iff : p ∈ (nil U β).Paths ↔ ∃ u ∈ U, Path.nil u = p := by
  simp only [nil, mem_image]

@[simp]
lemma nil_VxSet : (nil U β).VxSet = U := by
  simp only [VxSet, mem_nil_iff, Path.nil, vx, exists_exists_and_eq_and, nil_vx, mem_cons,
    not_mem_nil, or_false, exists_eq_right', setOf_mem_eq]

@[simp]
lemma nil_startSet : (nil U β).StartSet = U := by
  simp only [StartSet, start, nil, Path.nil, image_image, nil_start, image_id']

@[simp]
lemma nil_finishSet : (nil U β).FinishSet = U := by
  simp only [FinishSet, finish, nil, Path.nil, image_image, nil_finish, image_id']

@[simp]
lemma nil_ncard : (nil U β).Paths.ncard = U.ncard :=
  ncard_image_of_injective U nil_injective

@[simp]
lemma nil_encard : (nil U β).Paths.encard = U.encard :=
  nil_injective.encard_image _

lemma startSet_subset_VxSet : Ps.StartSet ⊆ Ps.VxSet := by
  rintro x ⟨p, hp, rfl⟩
  use p, hp, start_vx_mem

lemma finishSet_subset_VxSet : Ps.FinishSet ⊆ Ps.VxSet := by
  rintro x ⟨p, hp, rfl⟩
  use p, hp, finish_vx_mem

lemma ValidOn.vxSet_subset (hVd : Ps.ValidOn G) : Ps.VxSet ⊆ G.V := by
  rintro x ⟨p, hp, hx⟩
  exact (hVd p hp).mem_of_mem_vx hx

@[simp]
lemma nil_validOn_iff : (nil U β).ValidOn G ↔ U ⊆ G.V :=
  ⟨fun h ↦ by simpa using h.vxSet_subset, nil_validOn'⟩

-- dot notation
lemma startSet_subset_of_validOn (hVd : Ps.ValidOn G) : Ps.StartSet ⊆ G.V :=
  startSet_subset_VxSet.trans hVd.vxSet_subset

-- dot notation
lemma finishSet_subset_of_validOn (hVd : Ps.ValidOn G) : Ps.FinishSet ⊆ G.V :=
  finishSet_subset_VxSet.trans hVd.vxSet_subset

lemma mem_startSet_finishSet (hstart : x ∈ Ps.StartSet) (hfinish : x ∈ Ps.FinishSet) :
  ∃ p ∈ Ps.Paths, p = Path.nil x := by
  obtain ⟨q, hq, rfl⟩ := hfinish
  obtain ⟨p, hp, heq⟩ := hstart
  beta_reduce at heq
  obtain rfl := Ps.Disj p.val.start p q hp hq start_vx_mem (heq ▸ finish_vx_mem)
  simp only [start_eq_finish_iff, Nonempty.not_iff] at heq
  obtain ⟨x, hpnil⟩ := heq
  use p, hp
  rw [Subtype.ext_iff, hpnil]
  simp only [Path.nil, hpnil, nil_finish]

lemma StartSet_ncard : Ps.StartSet.ncard = Ps.Paths.ncard := by
  rw [eq_comm]
  apply Set.ncard_congr (fun p hp ↦ p.val.start)
  · rintro p hp
    use p
  · rintro p q hp hq hstart
    exact Ps.Disj p.val.start p q hp hq start_vx_mem (hstart ▸ start_vx_mem)
  · rintro x ⟨p, hp, rfl⟩
    use p

lemma FinishSet_ncard : Ps.FinishSet.ncard = Ps.Paths.ncard := by
  rw [eq_comm]
  apply Set.ncard_congr (fun p hp ↦ p.val.finish)
  · rintro p hp
    use p
  · rintro p q hp hq hfinish
    exact Ps.Disj p.val.finish p q hp hq finish_vx_mem (hfinish ▸ finish_vx_mem)
  · rintro x ⟨p, hp, rfl⟩
    use p

lemma ValidOn.le {G' : Graph α β} (h : G ≤ G') (hVd : Ps.ValidOn G) :
    Ps.ValidOn G' := fun p hp ↦ (hVd p hp).le h

lemma finite_of_finite_graph (h : G.Finite) (hVd : Ps.ValidOn G) : Ps.Paths.Finite := by
  have hle := (Ps.startSet_subset_VxSet).trans hVd.vxSet_subset
  have hst : Ps.StartSet.Finite := Finite.subset h.1 hle
  exact (finite_image_iff Ps.start_injOn).mp hst

@[simp]
lemma mem_insert_iff (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) :
    q ∈ (Ps.insert p h).Paths ↔ q = p ∨ q ∈ Ps.Paths := by
  simp only [insert, union_singleton, Set.mem_insert_iff]

lemma insert_validOn (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) (hVd : Ps.ValidOn G)
    (hpVd : p.val.ValidOn G) : (Ps.insert p h).ValidOn G := by
  rintro q hq
  rw [mem_insert_iff] at hq
  obtain (rfl | hq) := hq
  · exact hpVd
  · exact hVd q hq

@[simp]
lemma insert_ncard (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) (hFin : Ps.Paths.Finite) :
    (Ps.insert p h).Paths.ncard = Ps.Paths.ncard + 1 := by
  simp only [VxSet, mem_setOf_eq, not_exists, not_and, insert, union_singleton] at h ⊢
  refine Set.ncard_insert_of_not_mem (fun hp ↦ ?_) hFin
  obtain ⟨a, as, has⟩ := List.ne_nil_iff_exists_cons.mp (vx_ne_nil (w := p.val))
  specialize h a (by simp only [has, mem_cons, true_or]) p hp
  simp only [has, mem_cons, true_or, not_true_eq_false] at h

@[simp]
lemma insert_startSet (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) :
    (Ps.insert p h).StartSet = Ps.StartSet ∪ {p.val.start} := by
  simp only [StartSet, insert, union_singleton]
  exact image_insert_eq

@[simp]
lemma insert_finishSet (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) :
    (Ps.insert p h).FinishSet = Ps.FinishSet ∪ {p.val.finish} := by
  simp only [FinishSet, insert, union_singleton]
  exact image_insert_eq

@[simp]
lemma insert_VxSet (h : ∀ v ∈ p.val.vx, v ∉ Ps.VxSet) :
    (Ps.insert p h).VxSet = {u | u ∈ p.val.vx} ∪ Ps.VxSet := by
  ext x
  simp +contextual only [VxSet, insert, union_singleton, Set.mem_insert_iff, exists_eq_or_imp,
    mem_setOf_eq, mem_union]

lemma vx_dropLast_disjoint_FinishSet (p : Path α β) (hp : p ∈ Ps.Paths) :
    ∀ x ∈ p.val.vx.dropLast, x ∉ Ps.FinishSet := by
  rintro x hx ⟨q, hq, rfl⟩
  obtain rfl := Ps.Disj q.val.finish q p hq hp finish_vx_mem (List.mem_of_mem_dropLast hx)
  exact finish_not_mem_vx_dropLast hx

lemma vx_tail_disjoint_StartSet (p : Path α β) (hp : p ∈ Ps.Paths) :
    ∀ x ∈ p.val.vx.tail, x ∉ Ps.StartSet := by
  rintro x hx ⟨q, hq, rfl⟩
  obtain rfl := Ps.Disj q.val.start q p hq hp start_vx_mem (List.mem_of_mem_tail hx)
  exact start_not_mem_vx_tail hx

lemma validOn_induce_diff (hVd : Ps.ValidOn G) (hp : p ∈ Ps.Paths) :
    p.val.ValidOn (G - {x | ∃ p ∈ Ps.Paths \ {p}, x ∈ p.val.vx}) := by
  refine (hVd p hp).induce ?_
  rintro x hx
  refine ⟨(hVd p hp).mem_of_mem_vx hx, ?_⟩
  rintro ⟨q, hq, hxq⟩
  obtain rfl := Ps.Disj x q p hq.1 hp hxq hx
  simp only [mem_diff, mem_singleton_iff, not_true_eq_false, and_false] at hq

lemma finishSep_of_finishSetSep (hsep : G.IsVxSetSeparator Ps.FinishSet Ps.StartSet T)
    (hp : p ∈ Ps.Paths) (hVd : p.val.ValidOn G) :
    (G - {x | ∃ p ∈ Ps.Paths \ {p}, x ∈ p.val.vx}).IsVxSetSeparator {p.val.finish} Ps.StartSet T := by

  sorry

lemma vx_subset_leftHalf_of_FinishSetSep (hsep : G.IsVxSetSeparator Ps.FinishSet Ps.StartSet T)
    (hVd : Ps.ValidOn G) (p : Path α β) (hp : p ∈ Ps.Paths) {x : α} (hx : x ∈ p.val.vx) :
    x ∈ hsep.leftSet ∪ Ps.FinishSet := by
  sorry


lemma vx_dropLast_subset_leftSet_of_FinishSetSep (hsep : G.IsVxSetSeparator Ps.FinishSet Ps.StartSet T)
    (p : Path α β) (hp : p ∈ Ps.Paths) (hx : x ∈ p.val.vx.dropLast) : x ∈ hsep.leftSet := by

  sorry

lemma VxSet_subset_leftSet_of_FinishSetSep (hsep : G.IsVxSetSeparator Ps.FinishSet Ps.StartSet T) :
  Ps.VxSet ⊆ hsep.leftSet ∪ Ps.FinishSet := by
  rintro x ⟨p, hp, hx⟩

  sorry

variable {Ps₁ Ps₂ : PathEnsemble α β}

lemma append_validOn (hPs₁Vd : Ps₁.ValidOn G) (hPs₂Vd : Ps₂.ValidOn G)
    (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet) (heq : Ps₁.FinishSet = Ps₂.StartSet) :
    (Ps₁.append Ps₂ hsu heq).ValidOn G := by
  rintro p ⟨⟨a, ha⟩, _, rfl⟩
  refine Walk.append_validOn ?_ (hPs₁Vd _ (byFinish_mem ha)) (hPs₂Vd _ (byStart_mem (heq ▸ ha)))
  simp only [byFinish_finish, byStart_start]

@[simp]
lemma append_startSet (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) : (Ps₁.append Ps₂ hsu heq).StartSet = Ps₁.StartSet := by
  ext x
  simp +contextual only [StartSet, append, mem_image, Set.mem_range, Subtype.exists, iff_def,
    forall_exists_index, and_imp]
  constructor
  · rintro p u hu ⟨_, rfl⟩ rfl
    use Ps₁.byFinish u hu, byFinish_mem _, by simp only [byFinish_finish, byStart_start, append_start]
  · rintro p hp1 rfl
    use (Ps₁.byFinish p.val.finish (heq ▸ finish_mem_FinishSet hp1)).append
      (Ps₂.byStart p.val.finish <| heq ▸ finish_mem_FinishSet hp1) fun b ↦
      append_aux hsu (finish_mem_FinishSet hp1) (heq ▸ finish_mem_FinishSet hp1)
    use ?_, by simp only [hp1, byFinish_of_finish, byStart_start, append_start]
    use p.val.finish, finish_mem_FinishSet hp1

@[simp]
lemma append_finishSet (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) : (Ps₁.append Ps₂ hsu heq).FinishSet = Ps₂.FinishSet := by
  ext x
  simp +contextual only [FinishSet, append, mem_image, Set.mem_range, Subtype.exists, iff_def,
    forall_exists_index, and_imp]
  refine ⟨?_, ?_⟩
  · rintro p u q ⟨hq, rfl⟩ rfl rfl
    exact ⟨Ps₂.byStart q.val.finish (heq ▸ finish_mem_FinishSet hq), byStart_mem _, by rw [append_finish]⟩
  · rintro p hp rfl
    use (Ps₁.byFinish p.val.start (heq ▸ start_mem_StartSet hp)).append
      (Ps₂.byStart p.val.start <| heq ▸ start_mem_StartSet hp) fun b ↦
      append_aux hsu (heq ▸ start_mem_StartSet hp) (heq ▸ start_mem_StartSet hp)
    use ?_, by simp only [hp, byStart_of_start, append_finish]
    use p.val.start, ?_
    use Ps₁.byFinish p.val.start (heq ▸ start_mem_StartSet hp), byFinish_mem _, by simp only [byFinish_finish]

@[simp]
lemma append_ncard_eq_left (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) :
    (Ps₁.append Ps₂ hsu heq).Paths.ncard = Ps₁.Paths.ncard := by
  rw [← StartSet_ncard, append_startSet hsu heq, ← StartSet_ncard]

@[simp]
lemma append_ncard_eq_right (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) :
    (Ps₁.append Ps₂ hsu heq).Paths.ncard = Ps₂.Paths.ncard := by
  rw [← FinishSet_ncard, append_finishSet hsu heq, ← FinishSet_ncard]

lemma append_VxSet (hsu : Ps₁.VxSet ∩ Ps₂.VxSet ⊆ Ps₁.FinishSet)
    (heq : Ps₁.FinishSet = Ps₂.StartSet) :
  (Ps₁.append Ps₂ hsu heq).VxSet = Ps₁.VxSet ∪ Ps₂.VxSet := by
  ext x
  simp +contextual only [VxSet, append, Set.mem_range, Subtype.exists, mem_setOf_eq, mem_union]
  constructor
  · rintro ⟨p, ⟨u, hu, rfl⟩, hx⟩
    simp only [append_vx, mem_append] at hx
    refine hx.imp ?_ ?_
    · rintro h
      use Ps₁.byFinish u hu, byFinish_mem _, List.mem_of_mem_dropLast h
    · rintro h
      use Ps₂.byStart u (heq ▸ hu), byStart_mem _, h
  · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
    · use (Ps₁.byFinish p.val.finish <| finish_mem_FinishSet hp).append (Ps₂.byStart p.val.finish
        <| heq ▸ finish_mem_FinishSet hp) fun b ↦ append_aux hsu (finish_mem_FinishSet hp)
        (heq ▸ finish_mem_FinishSet hp), ?_, ?_
      use p.val.finish, finish_mem_FinishSet hp
      sorry
    · sorry


end PathEnsemble
