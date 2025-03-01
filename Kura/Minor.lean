import Kura.Subgraph


open Set Function
variable {α β : Type*} {G : Graph α β} {u v w x y : α} {e f g : β}
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

structure ContractSys.validOn (F : ContractSys α β) (G : Graph α β) : Prop where
  map_not_mem : ∀ ⦃x⦄, x ∉ G.V → F x = x
  map_connected : ∀ ⦃x⦄, x ∈ G.V → (G.restrict F.contractSet).Connected x (F x)
  map_edge : ∀ ⦃x y e⦄, e ∈ F.contractSet → G.Inc x e → G.Inc y e → F x = F y

lemma ContractSys.validOn.map_mem {F : ContractSys α β} {G : Graph α β} (h : F.validOn G) {x : α} :
    x ∈ G.V → F x ∈ G.V := by
  rintro hmem
  have := mem_of_connected' (h.map_connected hmem)
  simpa only [restrict] using this

-- def ContractSys.setoid (F : ContractSys α β) : Setoid α := Setoid.ker F

-- noncomputable def ContractSys.ofSetoid (r : Setoid α) (Sₑ : Set β) : ContractSys α β where
--   toFun a := (Quotient.mk r a).out
--   contractSet := Sₑ
--   idem a := by simp only [Quotient.out_eq]


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

@[simp]
lemma vx_mem_of_mem_contract {G : Graph α β} {m : ContractSys α β} {x : α} (hvalid : m.validOn G)
    (h : x ∈ (G.contract m hvalid).V) : x ∈ G.V := by
  obtain ⟨y, hy, rfl⟩ := h
  exact hvalid.map_mem hy

@[simp]
lemma not_mem_contract_of_not_mem {G : Graph α β} {m : ContractSys α β} {x : α} (hvalid : m.validOn G)
    (h : x ∉ G.V) : x ∉ (G.contract m hvalid).V := by
  contrapose! h
  exact vx_mem_of_mem_contract hvalid h



-- def Inc.contractFun (hxe : G.Inc x e) [DecidablePred (G.Inc · e)] : G.ContractFun where
--   toFun y := if G.Inc y e then x else y
--   contractSet := {e}
--   idem y := by
--     simp only
--     split_ifs <;>
--     simp
--   map_not_mem y hy := by
--     simp only
--     split_ifs with hy'
--     · exact False.elim <| hy hy'.vx_mem
--     rfl
--   map_connected y hy := by
--     simp only
--     split_ifs with hy'
--     ·
--   map_edge := _

def IsContraction (H G : Graph α β) := ∃ m hm, H = G.contract m hm

lemma isContraction_trans {G₁ G₂ G₃ : Graph α β} (hm : G₁.IsContraction G₂)
    (hm' : G₂.IsContraction G₃) : G₁.IsContraction G₃ := by
  obtain ⟨m21, hm21, rfl⟩ := hm
  obtain ⟨m32, hm32, rfl⟩ := hm'
  refine ⟨m21.comp m32 ?_, ?_, ?_⟩
  · rintro v
    by_cases h : v ∈ G₃.V
    · obtain ⟨w, hw, heq⟩ := hm21.map_mem (x := m32 v) (mem_image_of_mem m32 h)
      rw [← heq, m32.idem]
    · rw [hm21.map_not_mem, m32.idem]
      simp only [contract, mem_image, not_exists, not_and]
      rw [hm32.map_not_mem h]
      rintro x hx rfl
      exact h <| hm32.map_mem hx
  · refine ⟨?_, ?_, ?_⟩
    · rintro x hx
      simp only [ContractSys.comp]
      rw [hm32.map_not_mem hx, hm21.map_not_mem]
      exact not_mem_contract_of_not_mem hm32 hx
    · rintro x hxmem
      simp only [ContractSys.comp]
