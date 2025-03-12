import Kura.Subgraph
import Kura.Map


open Set Function
variable {α β α' α'' : Type*} {G H : Graph α β} {u v w x y : α} {e f g : β}
namespace Graph


structure ContractSys (α β α' : Type*) where
  toFun : α → α'
  contractSet : Set β

instance : CoeFun (ContractSys α β α') fun (_ : ContractSys α β α') ↦ α → α' where
  coe v := v.toFun

def contract (G : Graph α β) (m : ContractSys α β α') : Graph α' β :=
  (G.vxMap m){m.contractSetᶜ}
  -- V := m '' G.V
  -- E := G.E \ m.contractSet
  -- Inc v e := ∃ x, m x = v ∧ G.Inc x e ∧ e ∉ m.contractSet
  -- vx_mem_of_inc v e := by
  --   rintro ⟨x, rfl, h, -⟩
  --   exact ⟨x, h.vx_mem, rfl⟩
  -- edge_mem_of_inc v e := by
  --   rintro ⟨x, rfl, hx⟩
  --   exact ⟨hx.1.edge_mem, hx.2⟩
  -- exists_vertex_inc e he := by
  --   obtain ⟨v, hv⟩ := G.exists_vertex_inc he.1
  --   exact ⟨m v, v, rfl, hv, he.2⟩
  -- not_hypergraph _ _ _ e := by
  --   rintro ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩ ⟨z, rfl, hz⟩
  --   obtain h | h | h := G.not_hypergraph hx.1 hy.1 hz.1 <;>
  --   simp only [h, true_or, or_true]

notation G "/" m => Graph.contract G m

/- lemmas about ContractSys -/
namespace ContractSys

structure validOn (m : ContractSys α β α') (G : Graph α β) : Prop where
  map_not_mem : ∀ ⦃x y : α⦄, m x = m y → x ∉ G.V → x = y
  -- map_not_mem? : ∀ ⦃x y⦄, m x = m y → x ∉ G.V → y ∉ G.V
  map_connected : ∀ ⦃x y⦄, x ∈ G.V → (m x = m y ↔ G{m.contractSet}.Connected x y)

variable {n m : ContractSys α β α'}

@[ext]
lemma ext {m n : ContractSys α β α'} (h : m.toFun = n.toFun)
  (h' : m.contractSet = n.contractSet) : m = n := by
  obtain ⟨a, b⟩ := m
  obtain ⟨a', b'⟩ := n
  subst h h'
  rfl

@[simp]
lemma map_not_mem_simp (hm : m.validOn G) (hmeq : m x = m y) (hnin : x ∉ G.V) : x = y :=
  hm.map_not_mem hmeq hnin

lemma not_mem_of_map_eq_not_mem (hm : m.validOn G) (hmeq : m x = m y) (hnin : x ∉ G.V) : y ∉ G.V := by
  rw [← hm.map_not_mem hmeq hnin]
  exact hnin

@[simp]
lemma mem_of_map_eq_mem (hm : m.validOn G) (hmeq : m x = m y) (hx : x ∈ G.V) : y ∈ G.V := by
  by_contra! hy
  have := hm.map_not_mem hmeq.symm hy
  subst y
  exact hy hx

lemma map_eq_self_of_not_exist_inc (hm : m.validOn G) (hmeq : m x = m y)
    (hninc : ∀ e ∈ m.contractSet, ¬ G.Inc x e) : x = y := by
  by_cases hx : x ∈ G.V
  · refine eq_of_no_inc_edge_of_connected ?_ ((hm.map_connected hx).mp hmeq)
    rintro e ⟨hinc, hem⟩
    exact hninc e hem hinc
  · exact hm.map_not_mem hmeq hx

@[simp]
lemma map_mem (hx : x ∈ G.V) : m x ∈ (G/m).V := by
  use x

lemma map_eq_of_reflAdj (hm : m.validOn G) (hradj : G{m.contractSet}.reflAdj x y) : m x = m y := by
  obtain h | ⟨rfl, h⟩ := hradj
  · rw [hm.map_connected h.mem_left]
    exact h.connected
  · rfl

lemma validOn.of_inter_eq (hm : m.validOn G) (hf : m.toFun = n.toFun)
    (h : G.E ∩ m.contractSet = G.E ∩ n.contractSet) : n.validOn G where
  map_not_mem := by
    rw [← hf]
    exact hm.map_not_mem
  map_connected x y hx := by
    rw [← hf, (G.restrict_eq_restrict_iff n.contractSet m.contractSet).mpr h.symm]
    exact hm.map_connected hx

lemma toFun_eq_of_inter_eq_fixed_eq (hm : m.validOn G) (hn : n.validOn G)
    (hinter : G.E ∩ m.contractSet = G.E ∩ n.contractSet)
    (hfixed : ∀ v ∈ m '' G.V, ∃ x, n x = v ∧ m x = v) : ∀ x ∈ G.V, m x = n x := by
  rintro x hx
  obtain ⟨y, hny, hmy⟩ := hfixed (m x) (map_mem hx)
  have hy : y ∈ G.V := mem_of_map_eq_mem hm hmy.symm hx
  rwa [← hny, hn.map_connected hy, ← (G.restrict_eq_restrict_iff _ _).mpr hinter, ← hm.map_connected hy]

lemma validOn.le (hm : m.validOn G) (hle : H ≤ G) (hE : G.E ∩ m.contractSet ⊆ H.E) :
    m.validOn H := by
  constructor
  · intro v w hmeq hv
    apply m.map_eq_self_of_not_exist_inc hm hmeq
    rintro e he hinc
    rw [← Inc_iff_Inc_of_edge_mem_le hle (hE ⟨hinc.edge_mem, he⟩)] at hinc
    exact hv hinc.vx_mem
  · intro v w hv
    rw [hm.map_connected (vx_subset_of_le hle hv),
      restrict_Connected_iff_restrict_Connected_of_le hle hE hv]

lemma exists_of_contractSet (S : Set β) : ∃ m : ContractSys α β α, m.validOn G ∧
  S = m.contractSet := by
  have hdec : DecidablePred (· ∈ G.V) := Classical.decPred _
  let m : ContractSys α β α := {
    toFun := fun x ↦ if h : x ∈ G.V
      then ConnectedPartition.rep (G := G{S}) x h
      else x
    contractSet := S}
  use m, ?_
  constructor
  · intro u v hmeq hu
    simp only [hu, ↓reduceDIte, m] at hmeq
    subst u
    by_cases hv : v ∈ G.V
    · simp only [hv, ↓reduceDIte, m] at hu
      exfalso
      exact hu (ConnectedPartition.rep_mem (G := G{S}) hv)
    · simp only [hv, ↓reduceDIte, m]
  · rintro x y hx
    simp only [hx, ↓reduceDIte, m]
    constructor
    · rintro hmeq
      refine (ConnectedPartition.rep_connected (G := G{S}) hx).symm.trans ?_
      split_ifs at hmeq with h
      · convert (ConnectedPartition.rep_connected (G := G{S}) h)
      · subst y
        refine Connected.refl ?_
        apply ConnectedPartition.rep_mem
    · rintro hConn
      by_cases hy : y ∈ G.V
      · simp only [hy, ↓reduceDIte, m, ConnectedPartition.req_eq_iff_connected, hConn]
      · exfalso
        exact hy hConn.mem_right


/- Assuming m is valid on some G, m represents a set of the subgraphs to be contracted and
  for each subgraph, which vertex label to retain.
  This function restricts the set of subgraphs to only those that retains a vertex labels in R. -/
-- noncomputable def ContractSys.confine {m : ContractSys α β α'} (hmvalid : m.validOn G) (R : Set α) :
--     ContractSys α β α' where
--   toFun v := ite (m v ∈ R) (h := Classical.dec _) (m v) v
--   contractSet := {e ∈ m.contractSet | ∃ v, G.Inc v e ∧ m v ∈ R}

-- lemma ContractSys.validOn.confine {m : ContractSys α β} (hmvalid : m.validOn G) (R : Set α) :
--     (m.confine hmvalid R).validOn (G[m.toFun ⁻¹' R]) := by
--   constructor
--   · intro v hv
--     simp only [induce_V, mem_inter_iff, mem_preimage, not_and, ContractSys.confine, ite_eq_right_iff] at hv ⊢
--     rintro hinR
--     have : v ∉ G.V := fun a ↦ hv a hinR
--     exact hmvalid.map_not_mem_simp this
--   · simp only [induce_V, mem_inter_iff, mem_preimage, ContractSys.confine, induce_restrict_eq_subgraph,
--     and_imp]
--     rintro v hv hinR
--     simp only [hinR, ↓reduceIte]
--     have : G{{e | e ∈ m.contractSet ∧ ∃ v, G.Inc v e ∧ m.toFun v ∈ R}}[m.toFun ⁻¹' R] =
--       G{m.contractSet}[m.toFun ⁻¹' R] := by
--       ext x e
--       · simp only [induce_V, restrict_V, mem_inter_iff, mem_preimage]
--       · simp only [induce_E, restrict_E, restrict_inc, mem_setOf_eq, mem_preimage, and_imp,
--         forall_exists_index, mem_inter_iff]
--         constructor
--         · rintro ⟨⟨he, hin, v, hinc, hvR⟩, hR⟩
--           tauto
--         · rintro ⟨⟨he, hin⟩, h⟩
--           refine ⟨⟨he, hin, ?_⟩, ?_⟩
--           · obtain ⟨u, huin⟩ := G.exists_vertex_inc he
--             use u, huin, h u huin hin
--           · rintro a hainc _ b hbinc hbR
--             exact h a hainc hin
--       · simp only [induce_inc, restrict_inc, mem_setOf_eq, mem_preimage, and_imp,
--         forall_exists_index]
--         tauto
--     rw [this]; clear this
--     apply (hmvalid.map_connected hv).induce_of_mem
--     rintro x hxconn
--     simp only [mem_preimage]
--     rwa [← hmvalid.map_eq_of_connected hxconn]
--   · simp only [ContractSys.confine, mem_setOf_eq, induce_inc, mem_preimage, and_imp, forall_exists_index]
--     rintro x y e hem z hzinc hzR hxinc hinR hyinc hinR'
--     clear hzR hzinc z hinR'
--     simp only [hinR _ hxinc, ↓reduceIte, hinR _ hyinc]
--     exact hmvalid.map_edge hem hxinc hyinc

/- Creators of ContractSys -/

def id : ContractSys α β α where
  toFun := _root_.id
  contractSet := ∅

lemma id_validOn : ContractSys.id.validOn G where
  map_not_mem x y heq hnx := by
    simpa only using heq
  map_connected x y hx := by
    simp only [id, id_eq]
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact Connected.refl hx
    · rintro h
      refine eq_of_no_inc_edge_of_connected ?_ h
      rintro e
      simp only [restrict_E, inter_empty, mem_empty_iff_false, not_false_eq_true,
        not_inc_of_not_edge_mem]

end ContractSys

def Inc.contractSys (hxe : G.Inc x e) [DecidablePred (G.Inc · e)] : ContractSys α β α where
  toFun y := if G.Inc y e then x else y
  contractSet := {e}

lemma Inc.contractFun_validOn (hxe : G.Inc x e) [DecidablePred (G.Inc · e)] :
    (Inc.contractSys hxe).validOn G where
  map_not_mem a b heq hna := by
    simp_all only [contractSys, not_false_eq_true, not_inc_of_not_vx_mem, ite_false, ite_eq_right_iff]
    rintro hbinc
    simp_all only [ite_true, not_false_eq_true, not_inc_of_not_vx_mem]
  map_connected a b ha := by
    simp only [contractSys]
    split_ifs with hainc hbinc hbinc
    · simp only [true_iff]
      refine reflAdj.connected ?_
      refine Inc.reflAdj_of_inc ⟨hainc, rfl⟩ ⟨hbinc, rfl⟩
    · apply iff_of_false
      · rintro rfl
        exact hbinc hxe
      · rintro hconn
        have : a ≠ b := by
          rintro rfl
          exact hbinc hainc
        sorry
    · sorry
    · sorry




-- noncomputable def ContractSys.sup (m₁ m₂ : ContractSys G α') : ContractSys α β where
--   toFun v :=
--     let r := Setoid.ker m₁
--     let s := Setoid.ker m₂
--     let t := r ⊔ s
--     (Quotient.mk t v).out
--   contractSet := m₁.contractSet ∪ m₂.contractSet
--   idem _ := Quotient.mkout_idem

-- def ContractSys.comp (m : ContractSys G α') (h : ∀ v, m₂ (m₁ (m₂ v)) = m₁ (m₂ v)) :
--     ContractSys α β where
--   toFun v := m₁ (m₂ v)
--   contractSet := m₁.contractSet ∪ m₂.contractSet
--   idem _ := by simp only [h, m₁.idem]





-- lemma comp_symm_of_inter_eq {n m : ContractSys α β α} (hm : m.validOn G) (hn : n.validOn G)
--     (hinter : G.E ∩ m.contractSet = G.E ∩ n.contractSet) (v : α) :
--     m (n v) = n v → n (m v) = m v := by
--   rintro h
--   by_cases hv : v ∈ G.V
--   · have : G{n.contractSet}.Connected v (n v) := (hn.map_connected hv).mp
--     rw [(G.restrict_eq_restrict_iff n.contractSet m.contractSet).mpr hinter.symm] at this
--     have := hm.map_eq_of_connected this
--     rw [h] at this
--     rw [this, n.idem]
--   · rw [hm.map_not_mem hv, hn.map_not_mem hv]

-- lemma ContractSys.comp_comm_of_inter_eq {m : ContractSys α β} (hmvalid : m.validOn G)
--     {n : ContractSys α β} (hnvalid : n.validOn G) (hinter : G.E ∩ m.contractSet = G.E ∩ n.contractSet)
--     (v : α) : m (n v) = n v ↔ n (m v) = m v :=
--     ⟨ContractSys.comp_symm_of_inter_eq hmvalid hnvalid hinter v,
--     ContractSys.comp_symm_of_inter_eq hnvalid hmvalid hinter.symm v⟩

-- lemma ContractSys.toFun_eq_of_comp_eq_of_inter_eq {m : ContractSys α β} (hmvalid : m.validOn G)
--     {n : ContractSys α β} (hnvalid : n.validOn G) (h : ∀ v, n (m v) = m v)
--     (hinter : G.E ∩ m.contractSet = G.E ∩ n.contractSet) : m.toFun = n.toFun := by
--   ext x
--   by_cases hx : x ∈ G.V
--   · rw [← h]
--     have : G{m.contractSet}.Connected x (m x) := hmvalid.map_connected hx
--     rw [(G.restrict_eq_restrict_iff m.contractSet n.contractSet).mpr hinter] at this
--     exact (hnvalid.map_eq_of_connected this).symm
--   · rw [hmvalid.map_not_mem hx, hnvalid.map_not_mem hx]

-- lemma Inc.contractFun_validOn (hxinc : G.Inc x e) [DecidablePred (G.Inc · e)] :
--     hxinc.contractFun.validOn G where
--   map_not_mem y hynot := by
--     simp only [contractFun, ite_eq_right_iff]
--     exact fun hyinc ↦ False.elim <| hynot hyinc.vx_mem
--   map_connected y hy := by
--     simp only [contractFun]
--     split_ifs with hyinc <;> refine Relation.TransGen.single ?_ <;> unfold reflAdj
--     · split_ifs with h
--       · subst h
--         exact hy
--       · use e
--         simp only [restrict_inc, hyinc, mem_singleton_iff, and_self, hxinc]
--     · simp only [↓reduceIte, restrict_V, hy]
--   map_edge u v f hf huinc hvinc := by
--     simp only [contractFun, mem_singleton_iff] at hf
--     subst f
--     simp only [contractFun, huinc, ↓reduceIte, hvinc]








variable {m : ContractSys α β} (hvalid : m.validOn G)

@[simp]
lemma contract_V : (G.contract m).V = m '' G.V := rfl

@[simp]
lemma contract_E : (G.contract m).E = G.E \ m.contractSet := rfl

@[simp]
lemma contract_inc : (G.contract m).Inc v e ↔
    ∃ x, m x = v ∧ G.Inc x e ∧ e ∉ m.contractSet := by
  simp only [contract]

lemma contract_eq_vxMap_restrict :
    G.contract mabs_div_eq_leOnePart_sq = (G.vxMap m.toFun).edgeDel m.contractSet := by
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
lemma vx_mem_of_mem_contract (h : x ∈ (G/m).V) : x ∈ G.V := by
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

@[simp]
lemma contract_eq_self_iff : (G/m ~hvalid) = G ↔ G.E ∩ m.contractSet = ∅ := by
  constructor <;> rintro h
  · ext e
    rw [inter_comm]
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hem
    rw [← h]
    simp only [contract_E, mem_diff, hem, not_true_eq_false, and_false, not_false_eq_true]
  · have hmv : ∀ v ∈ G.V, m v = v := by
      intro v hv
      have := hvalid.map_connected hv
      rw [(G.restrict_eq_restrict_iff m.contractSet ∅).mpr, connected_comm] at this
      refine eq_of_no_inc_edge_of_connected ?_ this
      simp only [restrict_inc, mem_empty_iff_false, and_false, not_false_eq_true, implies_true]
      simp only [h, inter_empty]

    ext1
    · ext v
      simp only [contract_V]
      refine ⟨vx_mem_of_mem_contract hvalid, ?_⟩
      rintro hv
      use v, hv
      exact hmv v hv
    · simp only [contract_E, sdiff_eq_left]
      rwa [disjoint_iff_inter_eq_empty]
    · rename_i v e
      simp only [contract_inc]
      constructor
      · rintro ⟨x, rfl, hinc, hnin⟩
        rwa [hmv x hinc.vx_mem]
      · rintro hinc
        use v, hmv v hinc.vx_mem, hinc
        intro hin
        have : e ∈ G.E ∩ m.contractSet := ⟨hinc.edge_mem, hin⟩
        rwa [h] at this

@[simp]
lemma contract_id_eq_self : (G/ContractSys.id ~ContractSys.id_validOn) = G := by
  rw [contract_eq_self_iff]
  simp only [ContractSys.id, inter_empty]

@[simp]
lemma contract_eq_contract_iff (hmvalid : m.validOn G) {n : ContractSys α β}
    (hnvalid : n.validOn G) : (G/m ~hmvalid) = (G/n ~hnvalid) ↔
    m.toFun = n.toFun ∧ G.E ∩ m.contractSet = G.E ∩ n.contractSet := by
  constructor
  · rintro h
    have hE : G.E ∩ m.contractSet = G.E ∩ n.contractSet := by
      apply_fun Graph.E at h
      rw [contract_E, contract_E, Set.ext_iff] at h
      simp only [mem_diff, and_congr_right_iff] at h
      ext e
      simp only [mem_inter_iff, and_congr_right_iff]
      intro he
      specialize h e he
      exact not_iff_not.mp h

    refine ⟨?_, ?_⟩
    · apply ContractSys.toFun_eq_of_comp_eq_of_inter_eq hmvalid hnvalid ?_ hE
      rintro v
      by_cases hv : v ∈ G.V
      · have : m v ∈ (G/m ~hmvalid).V := by
          use v
        rw [h] at this
        obtain ⟨x, hx, hnxmv⟩ := this
        rw [← hnxmv, n.idem]
      · rw [hmvalid.map_not_mem hv, hnvalid.map_not_mem hv]
    · exact hE
  · rintro ⟨hf, hE⟩
    have hE' := Set.ext_iff.mp hE
    simp only [mem_inter_iff, and_congr_right_iff] at hE'
    ext1
    · simp only [contract_V, hf]
    · ext e
      simp only [contract_E, mem_diff, and_congr_right_iff] at hE' ⊢
      intro he
      exact not_congr (hE' e he)
    · simp only [contract_inc, hf]
      constructor
      · rintro ⟨x, rfl, hinc, hnin⟩
        use x, rfl, hinc
        rwa [← hE' _ hinc.edge_mem]
      · rintro ⟨x, rfl, hinc, hnin⟩
        use x, rfl, hinc
        rwa [hE' _ hinc.edge_mem]

@[simp]
lemma contract_restrict_eq_restrict_contract : (G/m ~hvalid){S} =
    (G{S ∪ (G.E ∩ m.contractSet)}/m ~(hvalid.of_le (G.restrict_le _) (by
    simp only [restrict_E, subset_inter_iff, inter_subset_left, subset_union_right, and_self]))) := by
  ext x e
  · simp only [restrict_V, contract_V, mem_image]
  · simp only [restrict_E, contract_E, mem_inter_iff, mem_diff, mem_union]
    tauto
  · simp only [restrict_inc, contract_inc, mem_union, mem_inter_iff]
    tauto

@[simp]
lemma contract_induce_eq_induce_contract : (G/m ~hvalid)[S] =
    (G[m ⁻¹' S]/(m.confine hvalid (m ⁻¹' S)) ~(by
    convert hvalid.confine (m.toFun ⁻¹' S) using 2
    ext v
    simp only [mem_preimage, m.idem])) := by
  ext x e
  · simp only [induce_V, contract_V, mem_inter_iff, mem_image, ContractSys.confine, mem_preimage]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hvS⟩
      use v, ⟨hv, hvS⟩
      have : m.toFun v ∈ m.toFun ⁻¹' S := by
        simp only [mem_preimage, m.idem, hvS]
      simp only [this, ↓reduceIte]
    · rintro ⟨v, ⟨hv, hvS⟩, rfl⟩
      have : m.toFun v ∈ m.toFun ⁻¹' S := by
        simp only [mem_preimage, m.idem, hvS]
      simp only [this, ↓reduceIte, hvS, and_true]
      use v
  · simp only [induce_E, contract_E, contract_inc, forall_exists_index, and_imp, mem_inter_iff,
    mem_diff, mem_setOf_eq, ContractSys.confine, mem_preimage, not_and, not_exists]
    constructor
    · rintro ⟨⟨hx, hnin⟩, hS⟩
      use ⟨hx, ?_⟩
      exact fun a x_1 a_1 a_2 ↦ hnin a
      rintro v hinc
      exact hS (m.toFun v) v rfl hinc hnin
    · rintro ⟨⟨hx, hS⟩, hnS⟩
      simp only [m.idem] at hnS
      use ⟨hx, ?_⟩
      · rintro a b rfl hinc hnin
        exact hS b hinc
      · rintro hin
        obtain ⟨v, hinc⟩ := G.exists_vertex_inc hx
        exact hnS hin v hinc (hS v hinc)
  · simp only [induce_inc, contract_inc, forall_exists_index, and_imp, ContractSys.confine,
    mem_preimage, mem_setOf_eq, not_and, not_exists]
    constructor
    · rintro ⟨⟨v, rfl, hinc, hnin⟩, hS⟩
      use v
      have : m.toFun v ∈ m.toFun ⁻¹' S := by
        simp only [mem_preimage, m.idem, (hS (m v) v rfl hinc hnin)]
      simp only [this, ↓reduceIte, true_and]; clear this
      use ⟨hinc, ?_⟩
      · exact fun a x a_1 a_2 ↦ hnin a
      · rintro x hinc
        exact hS (m.toFun x) x rfl hinc hnin
    · rintro ⟨y, rfl, ⟨hinc, hS⟩, hnS⟩
      simp only [m.idem] at hnS
      refine ⟨?_, ?_⟩
      · refine ⟨y, ?_, hinc, ?_⟩
        · have : m.toFun y ∈ m.toFun ⁻¹' S := by
            simp only [mem_preimage, m.idem]
            exact hS y hinc
          simp only [this, ↓reduceIte]
        · rintro hin
          exact hnS hin y hinc (hS y hinc)
      · rintro x z rfl hinc hnin
        exact hS z hinc

private lemma connected_restrict_of_reflAdj_restrict_contract (S : Set β)
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
  | single hadj => exact connected_restrict_of_reflAdj_restrict_contract hvalid S hadj
  | tail hconn hadj ih => exact ih.trans
    <| connected_restrict_of_reflAdj_restrict_contract hvalid S hadj

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

lemma contract_contract_compable {m : ContractSys α β} (hm : m.validOn G)
  {n : ContractSys α β} (hn : n.validOn (G/m ~hm)) :
  ∀ (v : α), m (n (m v)) = n (m v) := by
  rintro v
  by_cases h : v ∈ G.V
  · obtain ⟨w, hw, heq⟩ := hn.map_mem (x := m v) (mem_image_of_mem m h)
    rw [← heq, m.idem]
  · rw [hn.map_not_mem, m.idem]
    simp only [contract, mem_image, not_exists, not_and]
    rw [hm.map_not_mem h]
    rintro x hx rfl
    exact h <| hm.map_mem hx

lemma contract_contract_comp_validOn {m : ContractSys α β} (hm : m.validOn G)
    {n : ContractSys α β} (hn : n.validOn (G/m ~hm)) :
    (n.comp m (contract_contract_compable hm hn)).validOn G := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x hx
    simp only [ContractSys.comp]
    rw [hm.map_not_mem hx, hn.map_not_mem]
    exact not_mem_contract_of_not_vx_mem hm hx
  · rintro x hxmem
    simp only [ContractSys.comp]
    have hle := (G.restrict_mono m.contractSet (n.contractSet ∪ m.contractSet) subset_union_right)
    refine ((hm.map_connected hxmem).le hle).trans
      (?_ : G{n.contractSet ∪ m.contractSet}.Connected (m.toFun x) (n.toFun (m.toFun x)))
    rw [union_comm]
    apply Connected.restrict_of_connected_restrict_contract hm
    refine hn.map_connected (?_ : m x ∈ _)
    rwa [map_mem_contract_iff_vx_mem]
  · rintro x y e he hxinc hyinc
    simp only [ContractSys.comp] at he ⊢
    rw [union_comm, ← union_diff_self, mem_union] at he
    obtain he | he := he
    · congr 1
      exact hm.map_edge (e := e) he hxinc hyinc
    · apply hn.map_edge (e := e) (mem_of_mem_diff he) <;> simp only [contract]
      · use x, rfl, hxinc
        exact not_mem_of_mem_diff he
      · use y, rfl, hyinc
        exact not_mem_of_mem_diff he

@[simp]
lemma contract_contract_eq_contract_comp {m : ContractSys α β} (hm : m.validOn G)
  {n : ContractSys α β} (hn : n.validOn (G/m ~hm)) :
  ((G/m ~hm)/n ~hn) = G/(n.comp m (contract_contract_compable hm hn))
    ~(contract_contract_comp_validOn hm hn) := by
  ext x e <;> simp [contract_V, mem_image, exists_exists_and_eq_and, ContractSys.comp, contract_E,
    mem_diff, mem_union, not_or]
  · rw [and_assoc, @and_comm (x ∉ m.contractSet) (x ∉ n.contractSet)]
  · constructor
    · rintro ⟨v, rfl, ⟨w, rfl, hinc, henin32⟩, henin21⟩
      use w
    · rintro ⟨v, rfl, hinc, henin21, henin32⟩
      use m v, rfl, ?_
      use v



def Contract.toSubgraph {m : ContractSys α β} (hm : m.validOn G) (v : α) :
    Graph α β := G{m.contractSet}[m ⁻¹' {v}]



def IsContraction (H G : Graph α β) := ∃ m hm, H = G/m ~hm

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
  use m21.comp m32 (contract_contract_compable hm32 hm21), contract_contract_comp_validOn hm32 hm21
  exact contract_contract_eq_contract_comp hm32 hm21


def IsMinor (G H : Graph α β) := ∃ m, G ≤ H/m

notation G " ≤ₘ " H => IsMinor G H

lemma IsMinor.refl : G ≤ₘ G := by
  refine ⟨G.E, G.V, ContractSys.id, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [restrict_E_eq_self, induce_V_eq_self, ContractSys.id, id_eq, implies_true]
  · simp only [restrict_E_eq_self, induce_V_eq_self, ContractSys.id, id_eq]
    intro x hx
    apply Connected.refl
    exact hx
  · simp only [ContractSys.id, mem_empty_iff_false, restrict_E_eq_self, induce_V_eq_self, id_eq,
    IsEmpty.forall_iff, implies_true]
  · simp only [restrict_E_eq_self, induce_V_eq_self, contract_id_eq_self]

lemma IsMinor.trans {G H K : Graph α β} (hGH : G ≤ₘ H) (hHK : H ≤ₘ K) : G ≤ₘ K := by
  obtain ⟨R, U, m, hm, rfl⟩ := hGH
  obtain ⟨S, T, n, hn, rfl⟩ := hHK
  simp only [contract_restrict_eq_restrict_contract, induce_E, restrict_E, restrict_inc, and_imp,
    induce_restrict_eq_subgraph, restrict_restrict_eq_restrict_inter,
    contract_induce_eq_induce_contract, induce_induce_eq_induce_inter,
    contract_contract_eq_contract_comp]
  refine ⟨S ∩ (R ∪ K.E ∩ S ∩ {e | ∀ (x : α), K.Inc x e → e ∈ S → x ∈ T} ∩ n.contractSet),
    T ∩ n.toFun ⁻¹' U, _, _, rfl⟩
