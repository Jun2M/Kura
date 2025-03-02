import Kura.Subgraph


open Set Function
variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f g : β}
namespace Graph


def vxMap {α' : Type*} (G : Graph α β) (φ : α → α') : Graph α' β where
  V := φ '' G.V
  E := G.E
  Inc v e := ∃ v₀, φ v₀ = v ∧ G.Inc v₀ e
  vx_mem_of_inc v e := by
    rintro ⟨v₀, rfl, hv₀⟩
    exact mem_image_of_mem _ hv₀.vx_mem
  edge_mem_of_inc v e := by
    rintro ⟨v₀, rfl, hv₀⟩
    exact hv₀.edge_mem
  exists_vertex_inc e he := by
    obtain ⟨v, hv⟩ := G.exists_vertex_inc he
    exact ⟨φ v, v, rfl, hv⟩
  not_hypergraph x y z e := by
    rintro ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩ ⟨z, rfl, hz⟩
    obtain h | h | h := G.not_hypergraph hx hy hz <;>
    simp only [h, true_or, or_true]

structure ContractSys (α β : Type*) where
  toFun : α → α
  contractSet : Set β
  idem : ∀ x, toFun (toFun x) = toFun x

instance : CoeFun (ContractSys α β) fun (_ : ContractSys α β) ↦ α → α where
  coe v := v.toFun

@[simp]
def ContractSys.id : ContractSys α β where
  toFun := _root_.id
  contractSet := ∅
  idem := by simp only [id_eq, implies_true]

structure ContractSys.validOn (m : ContractSys α β) (G : Graph α β) : Prop where
  map_not_mem : ∀ ⦃x⦄, x ∉ G.V → m x = x
  map_connected : ∀ ⦃x⦄, x ∈ G.V → (G.restrict m.contractSet).Connected x (m x)
  map_edge : ∀ ⦃x y e⦄, e ∈ m.contractSet → G.Inc x e → G.Inc y e → m x = m y

@[simp]
lemma ContractSys.validOn.map_not_mem_simp {m : ContractSys α β} (h : m.validOn G) (hnin : x ∉ G.V) :
    m x = x := h.map_not_mem hnin

lemma ContractSys.validOn.map_mem {m : ContractSys α β} (h : m.validOn G) :
    x ∈ G.V → m x ∈ G.V := by
  rintro hmem
  have := (h.map_connected hmem).mem'
  simpa only [restrict] using this

def Inc.contractFun (hxe : G.Inc x e) [DecidablePred (G.Inc · e)] : ContractSys α β where
  toFun y := if G.Inc y e then x else y
  contractSet := {e}
  idem y := by
    simp only
    split_ifs <;>
    simp

lemma Inc.contractFun_validOn (hxinc : G.Inc x e) [DecidablePred (G.Inc · e)] :
    hxinc.contractFun.validOn G where
  map_not_mem y hynot := by
    simp only [contractFun, ite_eq_right_iff]
    exact fun hyinc ↦ False.elim <| hynot hyinc.vx_mem
  map_connected y hy := by
    simp only [contractFun]
    split_ifs with hyinc <;> refine Relation.TransGen.single ?_ <;> unfold reflAdj
    · split_ifs with h
      · subst h
        exact hy
      · use e
        simp only [restrict_inc, hyinc, mem_singleton_iff, and_self, hxinc]
    · simp only [↓reduceIte, restrict_V, hy]
  map_edge u v f hf huinc hvinc := by
    simp only [contractFun, mem_singleton_iff] at hf
    subst f
    simp only [contractFun, huinc, ↓reduceIte, hvinc]

noncomputable def ContractSys.sup (m₁ m₂ : ContractSys α β) : ContractSys α β where
  toFun v :=
    let r := Setoid.ker m₁
    let s := Setoid.ker m₂
    let t := r ⊔ s
    (Quotient.mk t v).out
  contractSet := m₁.contractSet ∪ m₂.contractSet
  idem _ := Quotient.mkout_idem

def ContractSys.comp (m₁ m₂ : ContractSys α β) (h : ∀ v, m₂ (m₁ (m₂ v)) = m₁ (m₂ v)) : ContractSys α β where
  toFun v := m₁ (m₂ v)
  contractSet := m₁.contractSet ∪ m₂.contractSet
  idem _ := by simp only [h, m₁.idem]

def contract (G : Graph α β) (m : ContractSys α β) (_hm : m.validOn G) : Graph α β where
  V := m '' G.V
  E := G.E \ m.contractSet
  Inc v e := ∃ x, m x = v ∧ G.Inc x e ∧ e ∉ m.contractSet
  vx_mem_of_inc v e := by
    rintro ⟨x, rfl, h, -⟩
    exact ⟨x, h.vx_mem, rfl⟩
  edge_mem_of_inc v e := by
    rintro ⟨x, rfl, hx⟩
    exact ⟨hx.1.edge_mem, hx.2⟩
  exists_vertex_inc e he := by
    obtain ⟨v, hv⟩ := G.exists_vertex_inc he.1
    exact ⟨m v, v, rfl, hv, he.2⟩
  not_hypergraph _ _ _ e := by
    rintro ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩ ⟨z, rfl, hz⟩
    obtain h | h | h := G.not_hypergraph hx.1 hy.1 hz.1 <;>
    simp only [h, true_or, or_true]

notation G "/" m " ~" hvalid => Graph.contract G m hvalid

variable {m : ContractSys α β} (hvalid : m.validOn G)

@[simp]
lemma contract_V : (G.contract m hvalid).V = m '' G.V := rfl

@[simp]
lemma contract_E : (G.contract m hvalid).E = G.E \ m.contractSet := rfl

@[simp]
lemma contract_inc : (G.contract m hvalid).Inc v e ↔
    ∃ x, m x = v ∧ G.Inc x e ∧ e ∉ m.contractSet := by
  simp only [contract]

lemma contract_eq_vxMap_restrict :
    G.contract m hvalid = (G.vxMap m.toFun).edgeDel m.contractSet := by
  ext1 <;> simp only [contract, edgeDel, restrict, vxMap, mem_diff, right_eq_inter]
  · exact diff_subset
  · constructor
    · rintro ⟨v, rfl, hinc, hnin⟩
      rename_i e
      use ?_, hinc.edge_mem
      use v
    · rintro ⟨⟨v, rfl, hinc⟩, he, hnin⟩
      use v

@[simp]
lemma vx_mem_of_mem_contract (h : x ∈ (G/m ~hvalid).V) : x ∈ G.V := by
  obtain ⟨y, hy, rfl⟩ := h
  exact hvalid.map_mem hy

@[simp]
lemma not_mem_contract_of_not_vx_mem (h : x ∉ G.V) : x ∉ (G/m ~hvalid).V := by
  contrapose! h
  exact vx_mem_of_mem_contract hvalid h

@[simp]
lemma map_mem_contract_iff_vx_mem : m x ∈ (G/m ~hvalid).V ↔ x ∈ G.V := by
  constructor <;> rintro h
  · obtain ⟨y, hy, heq⟩ := h
    by_contra! hnin
    rw [hvalid.map_not_mem hnin] at heq
    subst x
    exact hnin (hvalid.map_mem hy)
  · use x

private lemma connected_restrict_of_preconnected_restrict_contract (S : Set β)
    (h : (G/m ~hvalid){S}.reflAdj x y) : G{m.contractSet ∪ S}.Connected x y := by
  rw [reflAdj_iff_adj_or_eq] at h
  obtain ⟨e, hinc, h⟩ | ⟨rfl, hin⟩ := h
  · by_cases hx : x = y
    · subst x
      simp only [↓reduceIte] at h
      obtain ⟨v, hvinc, heq⟩ := h
      have := heq y hinc
      subst y
      refine Relation.TransGen.single ?_
      apply reflAdj_of_vxMem
      simp only [restrict_V]
      exact vx_mem_of_mem_contract hvalid hinc.vx_mem
    · simp only [hx, ↓reduceIte] at h
      obtain ⟨⟨y, rfl, hinc, hnin⟩, heS⟩ := hinc
      obtain ⟨⟨v, rfl, hvinc, _⟩, _⟩ := h
      have hle := (G.restrict_mono _ (m.contractSet ∪ S) subset_union_left)
      refine (hvalid.map_connected hinc.vx_mem).symm.le hle |>.trans ?_
      refine (?_ : G{m.contractSet ∪ S}.Connected y v).trans <| (hvalid.map_connected hvinc.vx_mem).le hle
      refine Connected.le ?_ (G.restrict_mono _ (m.contractSet ∪ S) subset_union_right)
      refine Relation.TransGen.single (Adj.reflAdj ?_)
      use e, ⟨hinc, heS⟩
      have : y ≠ v := fun a ↦ hx (congrArg m.toFun a)
      simp only [this, ↓reduceIte]
      exact ⟨hvinc, heS⟩
  · refine Relation.TransGen.single (reflAdj_of_vxMem ?_)
    obtain ⟨v, hv, rfl⟩ := hin
    simp only [restrict, mem_union, true_and]
    exact hvalid.map_mem hv

lemma Connected.restrict_of_connected_restrict_contract (S : Set β)
    (h : (G/m ~hvalid){S}.Connected x y) : G{m.contractSet ∪ S}.Connected x y := by
  induction h with
  | single hadj => exact connected_restrict_of_preconnected_restrict_contract hvalid S hadj
  | tail hconn hadj ih => exact ih.trans
    <| connected_restrict_of_preconnected_restrict_contract hvalid S hadj

lemma Connected.of_contract (h : (G/m ~hvalid).Connected x y) : G.Connected x y := by
  convert Connected.restrict_of_connected_restrict_contract hvalid Set.univ (x := x) (y := y) ?_ using 1
  · rw [eq_comm, restrict_eq_self_iff]
    exact diff_subset_iff.mp fun ⦃a⦄ a ↦ trivial
  · convert h
    rw [restrict_eq_self_iff]
    exact fun ⦃a⦄ a ↦ trivial

private lemma Connected.map_restrict_of_connected_restrict_contract_eq_eq (S : Set β)
    (h : (G/m ~hvalid){S}.Connected x y) :
    ∀ u v, m u = x → m v = y → G{m.contractSet ∪ S}.Connected u v := by
  have := Connected.restrict_of_connected_restrict_contract hvalid S (x := x) (y := y) h
  rintro u v rfl rfl
  have hle := (G.restrict_mono _ (m.contractSet ∪ S) subset_union_left)
  refine (?_ : G{m.contractSet ∪ S}.Connected u (m u)).trans (this.trans ?_)
  · refine (hvalid.map_connected ?_).le hle
    have := h.mem
    simpa only [restrict, map_mem_contract_iff_vx_mem] using this
  · refine (hvalid.map_connected ?_).le hle |>.symm
    have := h.mem'
    simpa only [restrict, map_mem_contract_iff_vx_mem] using this

lemma Connected.map_restrict_of_connected_restrict_contract (S : Set β)
    (h : (G/m ~hvalid){S}.Connected (m x) (m y)) : G{m.contractSet ∪ S}.Connected x y :=
  Connected.map_restrict_of_connected_restrict_contract_eq_eq hvalid S h _ _ rfl rfl

lemma Connected.map_of_connected_contract (h : (G/m ~hvalid).Connected (m x) (m y)) :
    G.Connected x y := by
  convert Connected.map_restrict_of_connected_restrict_contract hvalid Set.univ (x := x) (y := y) ?_
    using 1
  · simp only [restrict, union_univ, inter_univ, mem_univ, and_true]
  · convert h
    rw [restrict_eq_self_iff]
    exact fun ⦃a⦄ a ↦ trivial

lemma connected_contract_restrict_of_restrict_adj (S : Set β)
    (h : G{m.contractSet ∪ S}.reflAdj x u) :
    (G/m ~hvalid){S}.Connected (m.toFun x) (m.toFun u) := by
  by_cases hx : x = u
  · subst u
    refine Connected.refl ?_
    simp only [restrict, map_mem_contract_iff_vx_mem]
    rw [reflAdj_iff_adj_or_eq] at h
    obtain ⟨e, hinc, hnin⟩ | ⟨_, hin⟩ := h
    · have := hinc.vx_mem
      simpa only [restrict, mem_union] using this
    · simpa only [restrict, mem_union] using hin
  · simp only [reflAdj, Adj, hx, ↓reduceIte, false_and, or_false] at h
    obtain ⟨e, hxinc, huinc⟩ := h
    obtain ⟨he, hemS⟩ := hxinc.edge_mem
    rw [← union_diff_self] at hemS
    obtain hem | ⟨heS, hem⟩ := hemS
    · have hle := G.restrict_le (m.contractSet ∪ S)
      rw [hvalid.map_edge hem (hxinc.le hle) (huinc.le hle)]
      refine Connected.refl ?_
      simp only [restrict, map_mem_contract_iff_vx_mem]
      exact (huinc.le hle).vx_mem
    · refine Relation.TransGen.single ?_
      rw [reflAdj_iff_adj_or_eq]
      by_cases heq : m x = m u
      · right
        use heq
        simp only [restrict, map_mem_contract_iff_vx_mem]
        exact hxinc.vx_mem
      · left
        use e, ?_
        simp only [heq, ↓reduceIte, restrict, contract, heS, and_true]
        use u, rfl, huinc.1
        simp only [restrict, contract, heS, and_true]
        use x, rfl, hxinc.1

@[simp]
theorem Connected.map_restrict_iff_connected_restrict_contract {m : ContractSys α β}
    (hvalid : m.validOn G) (S : Set β) :
    (G.contract m hvalid){S}.Connected (m x) (m y) ↔ G{m.contractSet ∪ S}.Connected x y := by
  constructor
  · exact Connected.map_restrict_of_connected_restrict_contract hvalid S (x := x) (y := y)
  · rintro hconn
    induction hconn with
    | single hadj => exact connected_contract_restrict_of_restrict_adj hvalid S hadj
    | tail hconn hadj ih => exact ih.trans <| connected_contract_restrict_of_restrict_adj hvalid S hadj



def IsContraction (H G : Graph α β) := ∃ m hm, H = G.contract m hm

lemma IsContraction_refl : G.IsContraction G := by
  refine ⟨ContractSys.id, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [ContractSys.id, id_eq, implies_true]
  · simp only [ContractSys.id, id_eq]
    intro x hx
    apply Connected.refl
    exact hx
  · simp only [ContractSys.id, mem_empty_iff_false, id_eq, IsEmpty.forall_iff, implies_true]
  · simp only [contract, ContractSys.id, id_eq, image_id', diff_empty, mem_empty_iff_false,
    not_false_eq_true, and_true, exists_eq_left]

lemma isContraction_trans {G₁ G₂ G₃ : Graph α β} (hm : G₁.IsContraction G₂)
    (hm' : G₂.IsContraction G₃) : G₁.IsContraction G₃ := by
  obtain ⟨m21, hm21, rfl⟩ := hm
  obtain ⟨m32, hm32, rfl⟩ := hm'
  have hcompable : ∀ (v : α), m32.toFun (m21.toFun (m32.toFun v)) = m21.toFun (m32.toFun v) := by
    rintro v
    by_cases h : v ∈ G₃.V
    · obtain ⟨w, hw, heq⟩ := hm21.map_mem (x := m32 v) (mem_image_of_mem m32 h)
      rw [← heq, m32.idem]
    · rw [hm21.map_not_mem, m32.idem]
      simp only [contract, mem_image, not_exists, not_and]
      rw [hm32.map_not_mem h]
      rintro x hx rfl
      exact h <| hm32.map_mem hx
  refine ⟨m21.comp m32 hcompable, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro x hx
    simp only [ContractSys.comp]
    rw [hm32.map_not_mem hx, hm21.map_not_mem]
    exact not_mem_contract_of_not_vx_mem hm32 hx
  · rintro x hxmem
    simp only [ContractSys.comp]
    have hle := (G₃.restrict_mono m32.contractSet (m21.contractSet ∪ m32.contractSet) subset_union_right)
    refine ((hm32.map_connected hxmem).le hle).trans
      (?_ : G₃{m21.contractSet ∪ m32.contractSet}.Connected (m32.toFun x) (m21.toFun (m32.toFun x)))
    rw [union_comm]
    apply Connected.restrict_of_connected_restrict_contract hm32
    refine hm21.map_connected (?_ : m32 x ∈ _)
    rwa [map_mem_contract_iff_vx_mem]
  · rintro x y e he hxinc hyinc
    simp only [ContractSys.comp] at he ⊢
    rw [union_comm, ← union_diff_self, mem_union] at he
    obtain he | he := he
    · congr 1
      exact hm32.map_edge (e := e) he hxinc hyinc
    · apply hm21.map_edge (e := e) (mem_of_mem_diff he) <;> simp only [contract]
      · use x, rfl, hxinc
        exact not_mem_of_mem_diff he
      · use y, rfl, hyinc
        exact not_mem_of_mem_diff he
  · ext x e <;> simp [ContractSys.comp, contract]
    · rw [and_assoc, @and_comm (x ∉ m32.contractSet) (x ∉ m21.contractSet)]
    · constructor
      · rintro ⟨v, rfl, ⟨w, rfl, hinc, henin32⟩, henin21⟩
        use w
      · rintro ⟨v, rfl, hinc, henin21, henin32⟩
        use m32 v, rfl, ?_
        use v
