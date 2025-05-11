import Kura.Walk.Path

namespace Graph
open Set Function List Nat WList
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w1 w2 : WList α β}

namespace WList
section disjoint

/-- A collection of paths is internally disjoint if no vertex appears in more than one path
  except for the special two vertices u and v. (i.e. the endpoints of the paths. But this is not
  enforced in the definition) -/
def InternallyDisjoint (u v : α) (Ps : Set <| WList α β) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.vx → x ∈ pj.vx → pi ≠ pj → x = u ∨ x = v

/-- A collection of paths is disjoint if no vertex appears in more than one path -/
protected def Disjoint (Ps : Set <| WList α β) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.vx → x ∈ pj.vx → pi = pj

end disjoint
end WList

structure Ensemble (α β : Type*) where
  walks : Set (WList α β)
  disj : WList.Disjoint walks

namespace Ensemble

def empty (α β : Type*) : Ensemble α β where
  walks := ∅
  disj _ _ _ hp _ _ := hp.elim

def nil (U : Set α) (β : Type*) : Ensemble α β where
  walks := WList.nil '' U
  disj x p q hp hq hxp hxq := by
    simp only [mem_image] at hp hq
    obtain ⟨u, hu, rfl⟩ := hp
    obtain ⟨v, hv, rfl⟩ := hq
    simp only [vx, mem_cons, not_mem_nil, or_false] at hxp hxq
    subst u v
    rfl

def ValidIn (Ps : Ensemble α β) (G : Graph α β) := ∀ w ∈ Ps.walks, G.IsPath w

def firstSet (Ps : Ensemble α β) : Set α := (·.first) '' Ps.walks

def lastSet (Ps : Ensemble α β) : Set α := (·.last) '' Ps.walks

def vertexSet (Ps : Ensemble α β) : Set α := {x | ∃ w ∈ Ps.walks, x ∈ w}

def edgeSet (Ps : Ensemble α β) : Set β := {e | ∃ w ∈ Ps.walks, e ∈ w.edge}

def InternalVsSet (Ps : Ensemble α β) : Set α := {x | ∃ w ∈ Ps.walks, x ∈ w.tail.dropLast}

def insert (w : WList α β) (Ps : Ensemble α β) (h : ∀ v ∈ w, v ∉ Ps.vertexSet) : Ensemble α β where
  walks := Ps.walks ∪ {w}
  disj x p₁ p₂ hp1 hp2 hxp hxq := by
    simp only [union_singleton, Set.mem_insert_iff] at hp1 hp2
    simp only [vertexSet, mem_setOf_eq, not_exists, not_and] at h
    obtain (rfl | h1) := hp1 <;> obtain (rfl | h2) := hp2
    · rfl
    · exact (h x hxp p₂ h2 hxq).elim
    · exact (h x hxq p₁ h1 hxp).elim
    · exact Ps.disj x p₁ p₂ h1 h2 hxp hxq

lemma first_injOn (Ps : Ensemble α β) : InjOn (·.first) Ps.walks :=
  fun p₁ hp₁ p₂ hp₂ hfirst ↦ Ps.disj _ _ _ hp₁ hp₂ first_mem (by
    beta_reduce at hfirst
    exact hfirst ▸ first_mem)

lemma last_injOn (Ps : Ensemble α β) : InjOn (·.last) Ps.walks :=
  fun p₁ hp₁ p₂ hp₂ hlast ↦ Ps.disj _ _ _ hp₁ hp₂ last_mem (by
    beta_reduce at hlast
    exact hlast ▸ last_mem)

lemma unique_path_first (Ps : Ensemble α β)  :
    ∀ x ∈ Ps.firstSet, ∃! p ∈ Ps.walks, p.first = x := by
  rintro x ⟨p, hp, rfl⟩
  use p, ⟨hp, rfl⟩, (fun q hq ↦ first_injOn Ps hq.1 hp hq.2)

lemma unique_path_last (Ps : Ensemble α β) :
    ∀ x ∈ Ps.lastSet, ∃! p ∈ Ps.walks, p.last = x := by
  rintro x ⟨p, hp, rfl⟩
  use p, ⟨hp, rfl⟩, (fun q hq ↦ last_injOn Ps hq.1 hp hq.2)

noncomputable def byFirst (Ps : Ensemble α β) (u : α) (hu : u ∈ Ps.firstSet) : WList α β :=
  (Ps.unique_path_first u hu).choose

noncomputable def byLast (Ps : Ensemble α β) (u : α) (hu : u ∈ Ps.lastSet) : WList α β :=
  (Ps.unique_path_last u hu).choose

variable {Ps : Ensemble α β} {u : α}

@[simp]
lemma byFirst_mem {hu : u ∈ Ps.firstSet} : Ps.byFirst u hu ∈ Ps.walks :=
  (Ps.unique_path_first u hu).choose_spec.1.1

@[simp]
lemma byLast_mem {hu : u ∈ Ps.lastSet} : Ps.byLast u hu ∈ Ps.walks :=
  (Ps.unique_path_last u hu).choose_spec.1.1

@[simp]
lemma byFirst_first {hu : u ∈ Ps.firstSet} : (Ps.byFirst u hu).first = u :=
  (Ps.unique_path_first u hu).choose_spec.1.2

@[simp]
lemma byLast_last {hu : u ∈ Ps.lastSet} : (Ps.byLast u hu).last = u :=
  (Ps.unique_path_last u hu).choose_spec.1.2

lemma byFirst_injective (Ps : Ensemble α β) :
    Injective (fun a ↦ Ps.byFirst a.val a.prop : Ps.firstSet → WList α β) := by
  rintro x y h
  beta_reduce at h
  rw [Subtype.ext_iff, ← byFirst_first (hu := x.prop), h, byFirst_first (hu := y.prop)]

lemma byLast_injective (Ps : Ensemble α β) :
    Injective (fun a ↦ Ps.byLast a.val a.prop : Ps.lastSet → WList α β) := by
  rintro x y h
  beta_reduce at h
  rw [Subtype.ext_iff, ← byLast_last (hu := x.prop), h, byLast_last (hu := y.prop)]

variable {Ps Ps₁ Ps₂ : Ensemble α β} {u v x y : α} {p q : WList α β} {U S T : Set α}

@[simp]
lemma byFirst_inj (hu : u ∈ Ps.firstSet) (hv : v ∈ Ps.firstSet) :
    Ps.byFirst u hu = Ps.byFirst v hv ↔ u = v := by
  change (fun a ↦ Ps.byFirst a.val a.prop : Ps.firstSet → WList α β) ⟨u, hu⟩ = (fun a ↦ Ps.byFirst a.val a.prop : Ps.firstSet → WList α β) ⟨v, hv⟩ ↔ u = v
  rw [byFirst_injective Ps |>.eq_iff, Subtype.ext_iff]

@[simp]
lemma byLast_inj (hu : u ∈ Ps.lastSet) (hv : v ∈ Ps.lastSet) :
    Ps.byLast u hu = Ps.byLast v hv ↔ u = v := by
  change (fun a ↦ Ps.byLast a.val a.prop : Ps.lastSet → WList α β) ⟨u, hu⟩ = (fun a ↦ Ps.byLast a.val a.prop : Ps.lastSet → WList α β) ⟨v, hv⟩ ↔ u = v
  rw [byLast_injective Ps |>.eq_iff, Subtype.ext_iff]

lemma mem_vertexSet_mem (hu : u ∈ p) (hp : p ∈ Ps.walks) : u ∈ Ps.vertexSet := by
  use p, hp, hu

lemma mem_lastSet_mem (hu : u ∈ Ps.lastSet) (hup : u ∈ p) (hp : p ∈ Ps.walks) :
    u = p.last := by
  obtain ⟨q, hq, rfl⟩ := hu
  rw [Ps.disj q.last q p hq hp last_mem hup]

lemma mem_firstSet_mem (hv : v ∈ Ps.firstSet) (hvp : v ∈ p) (hp : p ∈ Ps.walks) :
    v = p.first := by
  obtain ⟨q, hq, rfl⟩ := hv
  rw [Ps.disj q.first q p hq hp first_mem hvp]

@[simp]
lemma first_mem_firstSet (hp : p ∈ Ps.walks) : p.first ∈ Ps.firstSet := by
  use p, hp

@[simp]
lemma last_mem_lastSet (hp : p ∈ Ps.walks) : p.last ∈ Ps.lastSet := by
  use p, hp

@[simp]
lemma byFirst_of_first (hp : p ∈ Ps.walks) : Ps.byFirst p.first (first_mem_firstSet hp) = p :=
  ((Ps.unique_path_first p.first (first_mem_firstSet hp)).choose_spec.2 p ⟨hp, rfl⟩).symm

@[simp]
lemma byLast_of_last (hp : p ∈ Ps.walks) : Ps.byLast p.last (last_mem_lastSet hp) = p :=
  ((Ps.unique_path_last p.last (last_mem_lastSet hp)).choose_spec.2 p ⟨hp, rfl⟩).symm

-- lemma append_aux {Ps₁ Ps₂ : Ensemble α β} (hsu : Ps₁.vertexSet ∩ Ps₂.vertexSet ⊆ Ps₁.lastSet)
--     (hu : u ∈ Ps₁.lastSet) (hv : v ∈ Ps₂.firstSet)
--     (hx1 : x ∈ (Ps₁.byLast u hu).vx.dropLast) (hx2 : x ∈ (Ps₂.byFirst v hv).vx) :
--     False := by
--   have hx1' : x ∈ Ps₁.vertexSet := by
--     use Ps₁.byLast u hu, byLast_mem hu, List.mem_of_mem_dropLast hx1
--   have hx2' : x ∈ Ps₂.vertexSet := by
--     use Ps₂.byFirst v hv, byFirst_mem hv, hx2
--   have := mem_lastSet_mem (hsu ⟨hx1', hx2'⟩) (List.mem_of_mem_dropLast hx1) (byLast_mem hu)
--   have := last_not_mem_dropLast_of_isPath
--   exact last_not_mem_vx_dropLast (this ▸ hx1)

def append (Ps₁ Ps₂ : Ensemble α β) (hsu : Ps₁.vertexSet ∩ Ps₂.vertexSet ⊆ Ps₁.lastSet)
    (heq : Ps₁.lastSet = Ps₂.firstSet) : Ensemble α β where
  walks :=
    let f : ↑(Ps₁.lastSet) → WList α β := fun ⟨a, ha⟩ ↦
      Ps₁.byLast a ha|>.append (Ps₂.byFirst a (heq ▸ ha))
        -- fun b ↦ append_aux hsu ha (heq ▸ ha)
    Set.range f
  disj x p q hp hq hxp hxq := by
    simp only [Set.mem_range, Subtype.exists] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    simp only [append_notation, append_vx, mem_append, mem_vx] at hxp hxq
    obtain (hxp1 | hxp2) := hxp <;> obtain (hxq1 | hxq2) := hxq
    · have := Ps₁.disj x _ _ byLast_mem byLast_mem (List.dropLast_subset _ hxp1) (List.dropLast_subset _ hxq1)
      rw [byLast_inj] at this
      subst b
      rfl
    · have := hsu ⟨mem_vertexSet_mem (dropLast_subset _ hxp1) byLast_mem, mem_vertexSet_mem hxq2 byFirst_mem⟩
      obtain rfl := byFirst_first ▸ mem_firstSet_mem (heq ▸ this) hxq2 byFirst_mem
      obtain rfl := byLast_last ▸ mem_lastSet_mem this (dropLast_subset _ hxp1) byLast_mem
      rfl
    · have := hsu ⟨mem_vertexSet_mem (dropLast_subset _ hxq1) byLast_mem, mem_vertexSet_mem hxp2 byFirst_mem⟩
      obtain rfl := byLast_last ▸ mem_lastSet_mem this (dropLast_subset _ hxq1) byLast_mem
      obtain rfl := byFirst_first ▸ mem_firstSet_mem (heq ▸ this) hxp2 byFirst_mem
      rfl
    · have := Ps₂.disj x _ _ byFirst_mem byFirst_mem hxp2 hxq2
      rw [byFirst_inj] at this
      subst b
      rfl

-- def appendOnSep (Ps₁ Ps₂ : PathEnsemble α β) (heq : Ps₁.lastSet = Ps₂.firstSet)
--     (hsep : G.IsvertexSetSeparator Ps₁.lastSet Ps₁.firstSet Ps₂.lastSet) : PathEnsemble α β :=
--   Ps₁.append Ps₂ (by
--     rintro x ⟨⟨p, hp1, hxp⟩, q, hq2, hxq⟩


--     rw [h1Finish] at hx
--     exact hsep.1 hx) (by
--     rintro x hx
--     rw [h2Start] at hx
--     exact hsep.2 hx)

@[simp]
lemma Empty_validIn : (empty α β).ValidIn G := by
  rintro p hp
  exact False.elim hp

@[simp]
lemma Empty_finite : (empty α β).walks.Finite := by
  simp only [empty, finite_empty]

@[simp]
lemma Empty_ncard : (empty α β).walks.ncard = 0 := by
  simp only [empty, ncard_empty]

@[simp]
lemma Empty_vertexSet : (empty α β).vertexSet = ∅ := by
  simp only [vertexSet, empty, mem_empty_iff_false, false_and, exists_false, setOf_false]

@[simp]
lemma Empty_edgeSet : (empty α β).edgeSet = ∅ := by
  simp only [edgeSet, empty, mem_empty_iff_false, false_and, exists_false, setOf_false]

@[simp]
lemma Empty_firstSet : (empty α β).firstSet = ∅ := by
  simp only [firstSet, empty, image_empty]

@[simp]
lemma Empty_lastSet : (empty α β).lastSet = ∅ := by
  simp only [lastSet, empty, image_empty]

@[simp]
lemma nil_validIn : (nil U β).ValidIn (G[U]) := by
  rintro p ⟨x, hx, rfl⟩
  simpa

@[simp]
lemma nil_validIn' (hUV : U ⊆ V(G)) : (nil U β).ValidIn G := by
  rintro p ⟨x, hx, rfl⟩
  simp only [nil_isPath_iff]
  exact hUV hx

@[simp]
lemma mem_nil_iff : p ∈ (nil U β).walks ↔ ∃ u ∈ U, WList.nil u = p := by
  simp only [nil, mem_image]

@[simp]
lemma nil_vertexSet : (nil U β).vertexSet = U := by
  simp only [vertexSet, mem_nil_iff, exists_exists_and_eq_and, WList.mem_nil_iff, exists_eq_right',
    setOf_mem_eq]

@[simp]
lemma nil_firstSet : (nil U β).firstSet = U := by
  simp only [firstSet, first, nil, image_image, image_id']

@[simp]
lemma nil_lastSet : (nil U β).lastSet = U := by
  simp only [lastSet, nil, image_image, last, image_id']

@[simp]
lemma nil_ncard : (nil U β).walks.ncard = U.ncard :=
  ncard_image_of_injective U nil_injective

@[simp]
lemma nil_encard : (nil U β).walks.encard = U.encard :=
  nil_injective.encard_image _

lemma firstSet_subset_vertexSet : Ps.firstSet ⊆ Ps.vertexSet := by
  rintro x ⟨p, hp, rfl⟩
  use p, hp, first_mem

lemma lastSet_subset_vertexSet : Ps.lastSet ⊆ Ps.vertexSet := by
  rintro x ⟨p, hp, rfl⟩
  use p, hp, last_mem

lemma ValidIn.vertexSet_subset (hVd : Ps.ValidIn G) : Ps.vertexSet ⊆ V(G) := by
  rintro x ⟨p, hp, hx⟩
  exact (hVd p hp).isWalk.vx_mem_of_mem hx

@[simp]
lemma nil_validIn_iff : (nil U β).ValidIn G ↔ U ⊆ V(G) :=
  ⟨fun h ↦ by simpa using h.vertexSet_subset, nil_validIn'⟩

lemma ValidIn.firstSet_subset (hVd : Ps.ValidIn G) : Ps.firstSet ⊆ V(G) :=
  firstSet_subset_vertexSet.trans hVd.vertexSet_subset

lemma ValidIn.lastSet_subset (hVd : Ps.ValidIn G) : Ps.lastSet ⊆ V(G) :=
  lastSet_subset_vertexSet.trans hVd.vertexSet_subset

lemma ValidIn.mem_firstSet_lastSet (hVd : Ps.ValidIn G) (hfirst : x ∈ Ps.firstSet)
    (hlast : x ∈ Ps.lastSet) : ∃ p ∈ Ps.walks, p = WList.nil x := by
  obtain ⟨q, hq, rfl⟩ := hlast
  obtain ⟨p, hp, heq⟩ := hfirst
  beta_reduce at heq
  obtain rfl := Ps.disj p.first p q hp hq first_mem (heq ▸ last_mem)
  rw [(hVd p hp).first_eq_last, nil_iff_eq_nil] at heq
  obtain ⟨x, rfl⟩ := heq
  use WList.nil x, hp
  simp

lemma firstSet_ncard : Ps.firstSet.ncard = Ps.walks.ncard := by
  rw [eq_comm]
  apply Set.ncard_congr (fun p hp ↦ p.first)
  · rintro p hp
    use p
  · rintro p q hp hq hfirst
    exact Ps.disj p.first p q hp hq first_mem (hfirst ▸ first_mem)
  · rintro x ⟨p, hp, rfl⟩
    use p

lemma lastSet_ncard : Ps.lastSet.ncard = Ps.walks.ncard := by
  rw [eq_comm]
  apply Set.ncard_congr (fun p hp ↦ p.last)
  · rintro p hp
    use p
  · rintro p q hp hq hlast
    exact Ps.disj p.last p q hp hq last_mem (hlast ▸ last_mem)
  · rintro x ⟨p, hp, rfl⟩
    use p

lemma ValidIn.of_le {G' : Graph α β} (h : G ≤ G') (hVd : Ps.ValidIn G) :
    Ps.ValidIn G' := fun p hp ↦ (hVd p hp).of_le h

lemma finite_of_finite_graph (h : G.Finite) (hVd : Ps.ValidIn G) : Ps.walks.Finite := by
  have hle := (Ps.firstSet_subset_vertexSet).trans hVd.vertexSet_subset
  have hst : Ps.firstSet.Finite := Finite.subset h.1 hle
  exact (finite_image_iff Ps.first_injOn).mp hst

@[simp]
lemma mem_insert_iff (h : ∀ v ∈ p, v ∉ Ps.vertexSet) :
    q ∈ (Ps.insert p h).walks ↔ q = p ∨ q ∈ Ps.walks := by
  simp only [insert, union_singleton, Set.mem_insert_iff]

lemma insert_validIn (h : ∀ v ∈ p, v ∉ Ps.vertexSet) (hVd : Ps.ValidIn G)
    (hpVd : G.IsPath p) : (Ps.insert p h).ValidIn G := by
  rintro q hq
  rw [mem_insert_iff] at hq
  obtain (rfl | hq) := hq
  · exact hpVd
  · exact hVd q hq

@[simp]
lemma insert_ncard (h : ∀ v ∈ p, v ∉ Ps.vertexSet) (hFin : Ps.walks.Finite) :
    (Ps.insert p h).walks.ncard = Ps.walks.ncard + 1 := by
  simp only [vertexSet, mem_setOf_eq, not_exists, not_and, insert, union_singleton] at h ⊢
  refine Set.ncard_insert_of_not_mem (fun hp ↦ ?_) hFin
  obtain ⟨a, as, has⟩ := List.ne_nil_iff_exists_cons.mp (vx_ne_nil (w := p))
  specialize h a (by simp [← mem_vx, has]) p hp
  simp [← mem_vx, has] at h

@[simp]
lemma insert_firstSet (h : ∀ v ∈ p, v ∉ Ps.vertexSet) :
    (Ps.insert p h).firstSet = Ps.firstSet ∪ {p.first} := by
  simp only [firstSet, insert, union_singleton]
  exact image_insert_eq

@[simp]
lemma insert_lastSet (h : ∀ v ∈ p, v ∉ Ps.vertexSet) :
    (Ps.insert p h).lastSet = Ps.lastSet ∪ {p.last} := by
  simp only [lastSet, insert, union_singleton]
  exact image_insert_eq

@[simp]
lemma insert_vertexSet (h : ∀ v ∈ p, v ∉ Ps.vertexSet) :
    (Ps.insert p h).vertexSet = {u | u ∈ p} ∪ Ps.vertexSet := by
  ext x
  simp +contextual only [vertexSet, insert, union_singleton, Set.mem_insert_iff, exists_eq_or_imp,
    mem_setOf_eq, mem_vx, mem_union]

lemma vx_dropLast_disjoint_lastSet (hp : p ∈ Ps.walks) (hP : G.IsPath p) :
    ∀ x ∈ p.vx.dropLast, x ∉ Ps.lastSet := by
  rintro x hx ⟨q, hq, rfl⟩
  obtain rfl := Ps.disj q.last q p hq hp last_mem (List.mem_of_mem_dropLast hx)
  simp at hx
  exact (vx_getLast ▸ hP.nodup.getLast_not_mem_dropLast vx_ne_nil) hx

lemma vx_tail_disjoint_firstSet (hp : p ∈ Ps.walks) (hP : G.IsPath p) :
    ∀ x ∈ p.vx.tail, x ∉ Ps.firstSet := by
  rintro x hx ⟨q, hq, rfl⟩
  obtain rfl := Ps.disj q.first q p hq hp first_mem (List.mem_of_mem_tail hx)
  exact (vx_head ▸ hP.nodup.head_not_mem_tail vx_ne_nil) hx

lemma validIn_induce_diff (hVd : Ps.ValidIn G) (hp : p ∈ Ps.walks) :
    (G - {x | ∃ p ∈ Ps.walks \ {p}, x ∈ p.vx}).IsPath p := by
  refine (hVd p hp).induce fun x hx ↦ ⟨(hVd p hp).isWalk.vx_mem_of_mem hx, ?_⟩
  rintro ⟨q, hq, hxq⟩
  obtain rfl := Ps.disj x q p hq.1 hp hxq hx
  simp only [mem_diff, mem_singleton_iff, not_true_eq_false, and_false] at hq

lemma lastSep_of_lastSetSep (hsep : G.IsVxSetSeparator Ps.lastSet Ps.firstSet T)
    (hp : p ∈ Ps.walks) (hVd : G.IsPath p) :
    (G - {x | ∃ p ∈ Ps.Paths \ {p}, x ∈ p.val.vx}).IsvertexSetSeparator {p.val.last} Ps.firstSet T := by

  sorry

lemma vx_subset_leftHalf_of_lastSetSep (hsep : G.IsvertexSetSeparator Ps.lastSet Ps.firstSet T)
    (hVd : Ps.ValidIn G) (p : Path α β) (hp : p ∈ Ps.Paths) {x : α} (hx : x ∈ p.val.vx) :
    x ∈ hsep.leftSet ∪ Ps.lastSet := by
  sorry


lemma vx_dropLast_subset_leftSet_of_lastSetSep (hsep : G.IsvertexSetSeparator Ps.lastSet Ps.firstSet T)
    (p : Path α β) (hp : p ∈ Ps.Paths) (hx : x ∈ p.val.vx.dropLast) : x ∈ hsep.leftSet := by

  sorry

lemma vertexSet_subset_leftSet_of_lastSetSep (hsep : G.IsvertexSetSeparator Ps.lastSet Ps.firstSet T) :
  Ps.vertexSet ⊆ hsep.leftSet ∪ Ps.lastSet := by
  rintro x ⟨p, hp, hx⟩

  sorry

variable {Ps₁ Ps₂ : Ensemble α β}

lemma append_validIn (hPs₁Vd : Ps₁.ValidIn G) (hPs₂Vd : Ps₂.ValidIn G)
    (hsu : Ps₁.vertexSet ∩ Ps₂.vertexSet ⊆ Ps₁.lastSet) (heq : Ps₁.lastSet = Ps₂.firstSet) :
    (Ps₁.append Ps₂ hsu heq).ValidIn G := by
  rintro p ⟨⟨a, ha⟩, _, rfl⟩
  have := hPs₁Vd (byLast Ps₁ a ha) byLast_mem
  simp
  refine append_isPath ?_  (hPs₂Vd _ (byFirst_mem (heq ▸ ha)))
  simp only [byLast_last, byFirst_first]

@[simp]
lemma append_firstSet (hsu : Ps₁.vertexSet ∩ Ps₂.vertexSet ⊆ Ps₁.lastSet)
    (heq : Ps₁.lastSet = Ps₂.firstSet) : (Ps₁.append Ps₂ hsu heq).firstSet = Ps₁.firstSet := by
  ext x
  simp +contextual only [firstSet, append, mem_image, Set.mem_range, Subtype.exists, iff_def,
    forall_exists_index, and_imp]
  constructor
  · rintro p u hu ⟨_, rfl⟩ rfl
    use Ps₁.byLast u hu, byLast_mem _, by simp only [byLast_last, byFirst_first, append_first]
  · rintro p hp1 rfl
    use (Ps₁.byLast p.val.last (heq ▸ last_mem_lastSet hp1)).append
      (Ps₂.byFirst p.val.last <| heq ▸ last_mem_lastSet hp1) fun b ↦
      append_aux hsu (last_mem_lastSet hp1) (heq ▸ last_mem_lastSet hp1)
    use ?_, by simp only [hp1, byLast_of_last, byFirst_first, append_first]
    use p.val.last, last_mem_lastSet hp1

@[simp]
lemma append_lastSet (hsu : Ps₁.vertexSet ∩ Ps₂.vertexSet ⊆ Ps₁.lastSet)
    (heq : Ps₁.lastSet = Ps₂.firstSet) : (Ps₁.append Ps₂ hsu heq).lastSet = Ps₂.lastSet := by
  ext x
  simp +contextual only [lastSet, append, mem_image, Set.mem_range, Subtype.exists, iff_def,
    forall_exists_index, and_imp]
  refine ⟨?_, ?_⟩
  · rintro p u q ⟨hq, rfl⟩ rfl rfl
    exact ⟨Ps₂.byFirst q.val.last (heq ▸ last_mem_lastSet hq), byFirst_mem _, by rw [append_last]⟩
  · rintro p hp rfl
    use (Ps₁.byLast p.val.first (heq ▸ first_mem_firstSet hp)).append
      (Ps₂.byFirst p.val.first <| heq ▸ first_mem_firstSet hp) fun b ↦
      append_aux hsu (heq ▸ first_mem_firstSet hp) (heq ▸ first_mem_firstSet hp)
    use ?_, by simp only [hp, byFirst_of_first, append_last]
    use p.val.first, ?_
    use Ps₁.byLast p.val.first (heq ▸ first_mem_firstSet hp), byLast_mem _, by simp only [byLast_last]

@[simp]
lemma append_ncard_eq_left (hsu : Ps₁.vertexSet ∩ Ps₂.vertexSet ⊆ Ps₁.lastSet)
    (heq : Ps₁.lastSet = Ps₂.firstSet) :
    (Ps₁.append Ps₂ hsu heq).Paths.ncard = Ps₁.Paths.ncard := by
  rw [← firstSet_ncard, append_firstSet hsu heq, ← firstSet_ncard]

@[simp]
lemma append_ncard_eq_right (hsu : Ps₁.vertexSet ∩ Ps₂.vertexSet ⊆ Ps₁.lastSet)
    (heq : Ps₁.lastSet = Ps₂.firstSet) :
    (Ps₁.append Ps₂ hsu heq).Paths.ncard = Ps₂.Paths.ncard := by
  rw [← lastSet_ncard, append_lastSet hsu heq, ← lastSet_ncard]

lemma append_vertexSet (hsu : Ps₁.vertexSet ∩ Ps₂.vertexSet ⊆ Ps₁.lastSet)
    (heq : Ps₁.lastSet = Ps₂.firstSet) :
  (Ps₁.append Ps₂ hsu heq).vertexSet = Ps₁.vertexSet ∪ Ps₂.vertexSet := by
  ext x
  simp +contextual only [vertexSet, append, Set.mem_range, Subtype.exists, mem_setOf_eq, mem_union]
  constructor
  · rintro ⟨p, ⟨u, hu, rfl⟩, hx⟩
    simp only [append_vx, mem_append] at hx
    refine hx.imp ?_ ?_
    · rintro h
      use Ps₁.byLast u hu, byLast_mem _, List.mem_of_mem_dropLast h
    · rintro h
      use Ps₂.byFirst u (heq ▸ hu), byFirst_mem _, h
  · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
    · use (Ps₁.byLast p.val.last <| last_mem_lastSet hp).append (Ps₂.byFirst p.val.last
        <| heq ▸ last_mem_lastSet hp) fun b ↦ append_aux hsu (last_mem_lastSet hp)
        (heq ▸ last_mem_lastSet hp), ?_, ?_
      use p.val.last, last_mem_lastSet hp
      sorry
    · sorry


end PathEnsemble
