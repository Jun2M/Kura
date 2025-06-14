import Kura.Operation.Hom


open Set Function Graph
variable {α β α' α'' β' : Type*} {G G' H H' : Graph α β} {u v w : α} {e f : β} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set β}


/-- The graph induced by a simple graph -/
@[simps]
def SimpleGraph.toGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  vertexSet := univ
  edgeSet := G.edgeSet
  IsLink e x y := s(x,y) = e ∧ G.Adj x y
  isLink_symm e x y := by simp [Sym2.eq_swap, SimpleGraph.adj_comm]
  vx_mem_left_of_isLink e x y := by simp
  edge_mem_iff_exists_isLink e := by
    refine ⟨fun he ↦ ?_, fun ⟨x, y, hx, he⟩ ↦ by simp [he, ← hx]⟩
    induction' e with x y
    use x, y
    simpa using he
  eq_or_eq_of_isLink_of_isLink a b c d e h1 h2 := by
    obtain ⟨rfl, he⟩ := h1
    obtain ⟨heq, he'⟩ := h2
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
    tauto

variable {G' H' : SimpleGraph α}

@[simp]
lemma SimpleGraph.toGraph_adj : (SimpleGraph.toGraph G').Adj = G'.Adj := by
  ext x y
  simp_rw [Graph.Adj, toGraph_isLink, exists_eq_left']

@[simp]
lemma SimpleGraph.toGraph_inj : G'.toGraph = H'.toGraph ↔ G' = H' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  ext x y
  rw [← toGraph_adj, ← toGraph_adj, h]


namespace Graph

class Loopless (G : Graph α β) : Prop where
  loopless x : ¬ G.Adj x x

lemma IsLoopless.of_le {G H : Graph α β} [G.Loopless] (hle : H ≤ G) : H.Loopless where
  loopless x := by
    rintro ⟨e, hbtw⟩
    exact Loopless.loopless x ⟨e, hbtw.of_le hle⟩

instance instLooplessGraphic : GraphicFunction Loopless Loopless where
  invariant h := by
    ext
    obtain ⟨g⟩ := h.symm
    obtain ⟨f⟩ := h
    refine ⟨fun hloop ↦ ⟨fun x ⟨e, hbtw⟩ ↦ ?_⟩, fun hloop ↦ ⟨fun x ⟨e, hbtw⟩ ↦ ?_⟩⟩
    · exact hloop.loopless (g.toFun ⟨x, hbtw.vx_mem_right⟩) ⟨g.edgeFun ⟨e, hbtw.edge_mem⟩, hbtw.isIsomOn g⟩
    · exact hloop.loopless (f.toFun ⟨x, hbtw.vx_mem_right⟩) ⟨f.edgeFun ⟨e, hbtw.edge_mem⟩, hbtw.isIsomOn f⟩

lemma IsLink.ne [hG : G.Loopless] (hbtw : G.IsLink e u v) : u ≠ v := by
  rintro rfl
  exact hG.loopless u ⟨e, hbtw⟩

lemma Adj.ne (G : Graph α β) [hS : G.Loopless] (huv : G.Adj u v) : u ≠ v := by
  rintro rfl
  exact hS.loopless u huv

@[simp]
lemma toSym2_not_isDiag {G : Graph α β} [G.Loopless] {e : β} {he : e ∈ E(G)} :
    ¬ (G.toSym2 e he).IsDiag := by
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  have := hxy.ne
  rwa [(toSym2_eq_pair_iff hxy.edge_mem).mpr hxy]

@[simps]
def deloop (G : Graph α β) : Graph α β where
  vertexSet := V(G)
  edgeSet := {e | ∃ x y, G.IsLink e x y ∧ x ≠ y}
  IsLink e x y := G.IsLink e x y ∧ x ≠ y
  isLink_symm _ _ _ h := by rwa [G.isLink_comm, ne_comm] at h
  vx_mem_left_of_isLink _ _ _ h := G.vx_mem_left_of_isLink h.1
  edge_mem_iff_exists_isLink _ := by simp only [ne_eq, mem_setOf_eq]
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := G.eq_or_eq_of_isLink_of_isLink h1.1 h2.1

instance instDeloopLoopless (G : Graph α β) : G.deloop.Loopless where
  loopless x := by
    rintro ⟨e, hbtw⟩
    simp only [deloop_isLink, ne_eq, not_true_eq_false, and_false] at hbtw

lemma deloop_edgeSet_subset : E(G.deloop) ⊆ E(G) := by
  rintro e he
  obtain ⟨x, y, hbtw, hne⟩ := he
  exact hbtw.edge_mem

lemma deloop_isLink_iff_of_mem_edgeSet (he : e ∈ E(G.deloop)) :
    G.deloop.IsLink e u v ↔ G.IsLink e u v := by
  refine ⟨(·.1), fun h ↦ ?_⟩
  obtain ⟨x, y, hbtw, hne⟩ := he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hbtw.eq_and_eq_or_eq_and_eq_of_isLink h
  · exact ⟨h, hne⟩
  · exact ⟨h, hne.symm⟩

@[simp↓]
lemma deloop_eq_self [G.Loopless] : G.deloop = G := by
  ext e x y
  · simp only [deloop_vertexSet]
  · simp only [deloop_isLink, ne_eq, and_iff_left_iff_imp]
    exact (·.ne)

lemma deloop_edgeSet_eq_edgeSet_iff_loopless : E(G.deloop) = E(G) ↔ G.Loopless := by
  refine ⟨fun h ↦ ⟨fun x hx ↦ ?_⟩, fun h ↦ by simp only [↓deloop_eq_self]⟩
  obtain ⟨e, hbtw⟩ := hx
  obtain he : e ∈ E(G.deloop) := h ▸ hbtw.edge_mem
  simpa using (deloop_isLink_iff_of_mem_edgeSet he).mpr hbtw |>.ne

@[simp]
lemma deloop_adj : G.deloop.Adj u v ↔ G.Adj u v ∧ u ≠ v := by
  simp only [Adj, deloop_isLink, ne_eq, exists_and_right]

@[simp]
lemma deloop_toSym2 (he : e ∈ E(G.deloop)) :
    G.deloop.toSym2 e he = G.toSym2 e (deloop_edgeSet_subset he) := by
  rw [toSym2_eq_toSym2_iff]
  ext _ _
  exact deloop_isLink_iff_of_mem_edgeSet he




class Simple (G : Graph α β) : Prop extends Loopless G where
  no_multi_edges e f : G.parallel e f → e = f

lemma Simple.of_le {G H : Graph α β} [G.Simple] (hle : H ≤ G) : H.Simple where
  loopless x := fun ⟨e, hbtw⟩ => Loopless.loopless x ⟨e, hbtw.of_le hle⟩
  no_multi_edges e f h := Simple.no_multi_edges e f (h.of_le hle)

@[simp]
lemma toSym2_inj [hG : G.Simple] (he : e ∈ E(G)) (hf : f ∈ E(G)) :
    G.toSym2 e he = G.toSym2 f hf ↔ e = f :=
  ⟨fun h ↦ hG.no_multi_edges e f ((G.parallel_iff_sym2_eq e f).mpr ⟨he, hf, h⟩), fun h ↦ h ▸ rfl⟩

@[simp]
lemma IsLink.edge_eq_iff_isLink [hG : G.Simple] (hbtw : G.IsLink e u v) :
    G.IsLink f u v ↔ e = f := by
  refine ⟨fun h ↦ ?_, (· ▸ hbtw)⟩
  obtain a := ((toSym2_eq_pair_iff hbtw.edge_mem).mpr hbtw).trans ((toSym2_eq_pair_iff h.edge_mem).mpr h).symm
  exact hG.no_multi_edges e f ((G.parallel_iff_sym2_eq e f).mpr ⟨hbtw.edge_mem, h.edge_mem, a⟩)

@[simp]
lemma not_simple_iff : ¬ G.Simple ↔ (∃ x, G.Adj x x) ∨ ∃ e f, G.parallel e f ∧ e ≠ f := by
  refine ⟨fun h ↦ ?_, fun h hsimp ↦ ?_⟩
  · contrapose! h
    exact {loopless := h.1, no_multi_edges := h.2}
  · obtain ⟨x, hadj⟩ | ⟨e, f, hpara, hne⟩ := h
    · exact hsimp.loopless x hadj
    · exact hne <| hsimp.no_multi_edges e f hpara

@[mk_iff]
class SimpleCanonical (G : Graph α (Sym2 α)) : Prop extends Simple G where
  canonical e he : G.toSym2 e he = e

instance instBotSimpleCanonical : SimpleCanonical (⊥ : Graph α (Sym2 α)) where
  loopless x := not_adj_of_right_notMem_vertexSet x fun a ↦ a
  no_multi_edges e f h := by simpa using h.1
  canonical e he := by simp at he

instance instNoEdgeSimpleCanonical : SimpleCanonical (Graph.noEdge S (Sym2 α)) where
  loopless x := not_adj_noEdge
  no_multi_edges e f h := by simpa using h.1
  canonical e he := by simp at he

@[simp]
lemma toSym2_eq_self {G : Graph α (Sym2 α)} [G.SimpleCanonical] {e : Sym2 α} {he : e ∈ E(G)} :
    G.toSym2 e he = e := SimpleCanonical.canonical e he

@[simp]
lemma isLink_iff_mem_edgeSet {G : Graph α (Sym2 α)} [G.SimpleCanonical] :
    G.IsLink s(u, v) u v ↔ s(u, v) ∈ E(G) := by
  refine ⟨IsLink.edge_mem, fun h ↦ ?_⟩
  rw [← toSym2_eq_pair_iff h]
  exact SimpleCanonical.canonical s(u, v) h

@[simp]
lemma isLink_iff_eq {G : Graph α (Sym2 α)} [G.SimpleCanonical] {e : Sym2 α} :
    G.IsLink e u v ↔ e = s(u, v) ∧ s(u, v) ∈ E(G) := by
  refine ⟨fun h ↦ ?_, fun ⟨he, h⟩ ↦ he ▸ isLink_iff_mem_edgeSet.mpr h⟩
  induction' e with x y
  have hxy := h.edge_mem
  rw [← toSym2_eq_pair_iff h.edge_mem, SimpleCanonical.canonical s(x, y)] at h
  exact ⟨h, h ▸ hxy⟩


instance instSimpleGraphic : GraphicFunction |₂ Simple where
  invariant {α β α' β' G G'} h := by
    ext
    refine ⟨fun hsimple ↦ {
      loopless := (instLooplessGraphic.invariant h ▸ hsimple.toLoopless).loopless
      no_multi_edges e f hpara := by
        obtain ⟨F⟩ := h
        have hpara' : G'.parallel (⟨e, hpara.left_mem⟩ : E(G')) (⟨f, hpara.right_mem⟩ : E(G')) := hpara
        rw [F.symm.parallel_iff] at hpara'
        have := hsimple.no_multi_edges _ _ hpara'
        rwa [Subtype.val_inj, F.symm.inj_edge.eq_iff, Subtype.ext_iff] at this}, fun hsimple ↦ {
      loopless := (instLooplessGraphic.invariant h ▸ hsimple.toLoopless).loopless
      no_multi_edges := fun e f hpara  ↦ by
        obtain ⟨F⟩ := h
        have hpara' : G.parallel (⟨e, hpara.left_mem⟩ : E(G)) (⟨f, hpara.right_mem⟩ : E(G)) := hpara
        rw [F.parallel_iff] at hpara'
        have := hsimple.no_multi_edges _ _ hpara'
        rwa [Subtype.val_inj, F.inj_edge.eq_iff, Subtype.ext_iff] at this}⟩

@[simps]
def toSimpleGraph (G : Graph α β) : SimpleGraph V(G) where
  Adj a b := a ≠ b ∧ G.Adj a b
  symm a b hab := by simpa only [ne_eq, eq_comm, adj_comm] using hab

@[simps! vertexSet]
def simplify (G : Graph α β) : Graph α (Sym2 α) :=
  oftoSym2 V(G) {s | ¬ s.IsDiag ∧ ∃ (e : β) (he : e ∈ E(G)), G.toSym2 e he = s}
    (fun e _ ↦ e) (fun e x ⟨f, hf, h, hdiag⟩ hx ↦ by subst e; exact vx_mem_of_toSym2 hx)

-- @[simps! vertexSet edgeSet]
-- def Simplify (G : Graph α β) : Graph α (Sym2 α) :=
--   oftoSym2 V(G) {s | ∃ u v, s(u, v) = s ∧ u ≠ v ∧ G.Adj u v}
--     (fun e _ ↦ e) (fun e x ⟨u, v, h, hne, hadj⟩ hx ↦ by
--     subst e
--     simp at hx
--     obtain (rfl | rfl) := hx
--     · exact hadj.mem_left
--     · exact hadj.mem_right)

instance instSimplifyVxSetFinite (G : Graph α β) [Finite V(G)] : Finite V(G.simplify) := by
  rw [simplify_vertexSet]
  infer_instance

@[simp]
lemma Simplify_edgeSet : E(G.simplify) = {s | ¬s.IsDiag ∧ ∃ x, ∃ (x_1 : x ∈ E(G)), G.toSym2 x x_1 = s} := by
  unfold simplify
  simp only [mem_setOf_eq, oftoSym2_edgeSet, exists_and_right]

lemma simplify_edgeSet_subset_range_toSym2 :
    E(G.simplify) ⊆ Set.range (fun a ↦ G.toSym2 a.1 a.2 : E(G) → _) := by
  rintro s hs
  simp only [Simplify_edgeSet, mem_setOf_eq] at hs
  obtain ⟨hdiag, e, he, rfl⟩ := hs
  use ⟨e, he⟩

lemma simplify_edgeSet_eq_range_toSym2 [G.Loopless]:
    E(G.simplify) = Set.range (fun a ↦ G.toSym2 a.1 a.2 : E(G) → _) := by
  apply subset_antisymm simplify_edgeSet_subset_range_toSym2
  rintro s hs
  simp only [mem_range, Subtype.exists] at hs
  obtain ⟨e, he, rfl⟩ := hs
  simp only [Simplify_edgeSet, mem_setOf_eq, toSym2_not_isDiag, not_false_eq_true,
    toSym2_eq_toSym2_iff_parallel, exists_prop, true_and]
  use e, he, he

lemma card_simplify_edgeSet_le (G : Graph α β) [Finite E(G)] :
    E(G.simplify).ncard ≤ E(G).ncard := by
  refine le_trans ?_ <| Finite.card_range_le (fun a ↦ G.toSym2 a.1 a.2)
  rw [Set.Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard simplify_edgeSet_subset_range_toSym2

instance instSimplifyFinite (G : Graph α β) [Finite E(G)] : Finite E(G.simplify) :=
  Set.finite_range (fun a ↦ G.toSym2 a.1 a.2 : E(G) → _)
  |>.subset simplify_edgeSet_subset_range_toSym2

lemma simplify_edgeSet_adj {G : Graph α β} : E(G.simplify) = {s | ∃ u v, s(u, v) = s ∧ u ≠ v ∧ G.Adj u v} := by
  ext s
  simp only [simplify, mem_setOf_eq, oftoSym2_edgeSet, exists_and_right, ← ne_eq]
  constructor
  · rintro ⟨hdiag, e, he, hs⟩
    induction' s with x y
    use x, y, rfl, hdiag, e, by rwa [toSym2_eq_pair_iff] at hs
  · rintro ⟨u, v, rfl, hdiag, e, hbtw⟩
    exact ⟨hdiag, e, hbtw.edge_mem, hbtw.toSym2⟩

@[simp]
lemma simplify_isLink {G : Graph α β} (e : Sym2 α) (x y : α) :
    G.simplify.IsLink e x y ↔ x ≠ y ∧ G.Adj x y ∧ e = s(x, y) := by
  simp only [simplify, mem_setOf_eq, oftoSym2_isLink, exists_and_right, exists_prop, ne_eq]
  rw [← and_assoc (a := x ≠ y), and_congr_left_iff]
  rintro rfl
  simp only [toSym2_eq_pair_iff, exists_prop, Sym2.isDiag_iff_proj_eq, Adj, ne_eq,
    and_congr_right_iff]
  rintro hne
  refine ⟨fun ⟨e, he, hbtw⟩ ↦ ?_, fun ⟨e, hbtw⟩ ↦ ?_⟩
  · use e
  · use e, hbtw.edge_mem

@[simp]
lemma simplify_adj : (simplify G).Adj u v ↔ u ≠ v ∧ G.Adj u v := by
  simp only [Adj, simplify, mem_setOf_eq, oftoSym2_isLink, exists_and_right, exists_prop,
    exists_eq_right, toSym2_eq_pair_iff, Sym2.isDiag_iff_proj_eq, ← ne_eq]
  rw [and_congr_right_iff]
  exact fun hne ↦ exists_congr fun e ↦ and_iff_right_iff_imp.mpr (IsLink.edge_mem ·)

@[simp]
lemma simplify_toSym2 {G : Graph α β} {e : Sym2 α} (he : e ∈ E(simplify G)) :
    (simplify G).toSym2 e he = e := by
  induction' e with x y
  simp only [Simplify_edgeSet, mem_setOf_eq, toSym2_eq_pair_iff, simplify_isLink, ne_eq,
    and_true] at he ⊢
  obtain ⟨hdiag, e, he, h⟩ := he
  exact ⟨hdiag, e, h⟩

instance instSimpleCanonicalSimplify : SimpleCanonical (simplify G) where
  loopless x := by
    simp only [Adj, simplify, mem_setOf_eq, oftoSym2_isLink, exists_prop, exists_eq_right,
      Sym2.isDiag_iff_proj_eq, not_true_eq_false, toSym2_eq_pair_iff, false_and, not_false_eq_true]
  no_multi_edges e f h := by
    rw [parallel_iff_sym2_eq] at h
    obtain ⟨he, hf, h⟩ := h
    simpa only [simplify, mem_setOf_eq, oftoSym2_tosym2] using h
  canonical e he := by simp only [simplify, mem_setOf_eq, oftoSym2_tosym2]

@[simp]
lemma deloop_simplify_eq_simplify : G.deloop.simplify = G.simplify := by
  ext e x y
  · simp only [simplify_vertexSet, deloop_vertexSet]
  · simp +contextual only [isLink_iff_eq, Simplify_edgeSet, deloop_toSym2, deloop_edgeSet, ne_eq,
    mem_setOf_eq, Sym2.isDiag_iff_proj_eq, toSym2_eq_pair_iff, exists_prop, and_congr_right_iff]
    rintro rfl (hne : x ≠ y)
    refine ⟨fun ⟨e, _, hbtw⟩ ↦ ?_, fun ⟨e, he, hbtw⟩ ↦ ?_⟩
    · use e, hbtw.edge_mem
    · use e, by use x, y

lemma simplify_hasIsom [hG : G.Simple] : G ↔ᴳ G.simplify := ⟨{
  toFun := id
  edgeFun e := ⟨G.toSym2 e e.prop, by
    rw [Simplify_edgeSet]
    simp only [mem_setOf_eq, toSym2_not_isDiag, not_false_eq_true, toSym2_inj, exists_prop,
      exists_eq_right, Subtype.coe_prop, and_self]⟩
  isLink e x y hbtw := by
    simp only [simplify_vertexSet, id_eq, isLink_iff_eq, toSym2_eq_pair_iff, hbtw,
      simplify_edgeSet_adj, ne_eq, mem_setOf_eq, true_and]
    use x, y, rfl, hbtw.ne, e, hbtw
  invFun := id
  vx_left_inv := congrFun rfl
  vx_right_inv := congrFun rfl
  edgeInvFun e := by
    obtain he := by simpa only [Simplify_edgeSet, ne_eq, mem_setOf_eq] using e.prop
    use he.2.choose, he.2.choose_spec.choose
  edge_left_inv e := by
    have : G.toSym2 ↑e e.prop ∈ E(G.simplify) := by
      rw [Simplify_edgeSet]
      simp only [mem_setOf_eq, toSym2_not_isDiag, not_false_eq_true, toSym2_inj, exists_prop,
        exists_eq_right, Subtype.coe_prop, and_self]
    obtain he := by simpa only [Simplify_edgeSet, ne_eq, mem_setOf_eq] using this
    rw [Subtype.ext_iff]
    exact (toSym2_inj he.2.choose_spec.choose e.prop).mp he.2.choose_spec.choose_spec
  edge_right_inv e := by
    obtain he := by simpa only [Simplify_edgeSet, ne_eq, mem_setOf_eq] using e.prop
    rw [Subtype.ext_iff]
    exact he.2.choose_spec.choose_spec}⟩

lemma simplify_edgeSet_ncard_eq_iff_simple (G : Graph α β) [hE : Finite E(G)] :
    E(G.simplify).ncard = E(G).ncard ↔ G.Simple := by
  refine ⟨fun h ↦ ?_, fun h ↦ G.simplify_hasIsom.symm.eq |₂ (fun G ↦ E(G).ncard)⟩
  have : G.Loopless := by
    rw [← deloop_simplify_eq_simplify] at h
    have h1 : E(G.deloop).ncard ≤ E(G).ncard := ncard_le_ncard deloop_edgeSet_subset hE
    have h1fin : Finite E(G.deloop) := Finite.subset hE deloop_edgeSet_subset
    have h2 : E(G.deloop.simplify).ncard ≤ E(G.deloop).ncard := card_simplify_edgeSet_le G.deloop
    rw [h] at h2
    have H : E(G.deloop) = E(G) := eq_of_subset_of_ncard_le deloop_edgeSet_subset (le_antisymm h1 h2).ge
    rwa [deloop_edgeSet_eq_edgeSet_iff_loopless] at H

  rw [simplify_edgeSet_eq_range_toSym2] at h
  have : Injective (fun a ↦ G.toSym2 a.1 a.2 : E(G) → _) := by
    rw [injective_iff_injOn_univ, ← ncard_image_iff finite_univ]
    convert h <;> simp

  refine ⟨fun e f hef ↦ ?_⟩
  rw [parallel_iff_sym2_eq] at hef
  obtain ⟨he, hf, heq⟩ := hef
  obtain H := @this ⟨e, he⟩ ⟨f, hf⟩ heq
  rwa [Subtype.ext_iff] at H

lemma simplify_eq_edgeMap [hα : Nonempty α] [hG : G.Simple] [DecidablePred (· ∈ E(G))] :
    G.simplify = G.edgeMap (fun e ↦ if he : e ∈ E(G) then G.toSym2 e he else s(hα.some, hα.some))
    (fun e he f hf => by simp [he, hf]; apply hG.no_multi_edges e f) := by
  refine Graph.ext_toSym2 rfl ?_ fun e he => ?_
  · ext e
    rw [Simplify_edgeSet]
    simp only [mem_setOf_eq, edgeMap_edgeSet, mem_image]
    constructor
    · rintro ⟨hne, f, hf, rfl⟩
      use f, hf, by simp [hf]
    · rintro ⟨f, hf, he⟩
      obtain rfl := by simpa [hf] using he
      refine ⟨?_, f, hf, rfl⟩
      exact toSym2_not_isDiag
  · obtain ⟨hne, f, hf, rfl⟩ := by rwa [Simplify_edgeSet, mem_setOf] at he
    simp only [toSym2_eq_self]
    refine ((G.toSym2 f hf).eq_mk_out).trans ?_
    rw [eq_comm, toSym2_eq_pair_iff, edgeMap_isLink]
    use f, by simp [hf]
    rw [← toSym2_eq_pair_iff hf, ← Sym2.eq_mk_out]

lemma simplify_vertexIsom [hα : Nonempty α] [hG : G.Simple] :
    ∃ (F : G.Isom G.simplify), Subtype.val ∘ F.toFun = Subtype.val := by
  classical
  let F := (simplify_eq_edgeMap (G := G)) ▸ edgeMap_isom _ _
  refine ⟨F, ?_⟩
  ext v
  simp only [simplify_vertexSet, comp_apply]
  unfold F

  sorry

-- lemma simplify_vertexIsom [hα : Nonempty α] [hG : G.Simple] :
--     ∃ (f : β → Sym2 α) (hf : InjOn f E(G)), G.edgeMap f hf = G.simplify := by
--   classical
--   use (fun e => if he : e ∈ E(G) then G.toSym2 e he else s(hα.some, hα.some)),
--     (fun e he f hf => by simp [he, hf]), simplify_eq_edgeMap.symm

-- lemma simplify_vertexIsom [Nonempty α] [hG : G.Simple] :
--     ∃ f : β → Sym2 α, (Funs.ofEdgeFun f).IsIsomOn G G.Simplify := by
--   classical
--   refine ⟨fun e ↦ if he : e ∈ E(G) then G.toSym2 e he else s(hα.some, hα.some), ⟨?_, ?_, ?_⟩⟩
--   · refine {
--       Mapsto_vx := fun x ↦ by simp,
--       isLink := fun e x y hxy ↦ by
--         simp only [HomSys.ofEdgeFun_edgeFun, hxy.edge_mem, ↓reduceDIte, HomSys.ofEdgeFun_toFun,
--           id_eq, isLink_iff_eq, toSym2_eq_pair_iff, hxy, simplify_edgeSet_adj, mem_setOf_eq, true_and]
--         use x, y, rfl, hxy.ne, e, hxy}
--   · rw [Simplify_vertexSet]
--     exact bijOn_id V(G)
--   · rw [Simplify_edgeSet]
--     refine ⟨?_, ?_, ?_⟩
--     · rintro e he
--       simp only [HomSys.ofEdgeFun_edgeFun, he, ↓reduceDIte, mem_setOf_eq, toSym2_not_isDiag,
--         not_false_eq_true, toSym2_inj, exists_prop, exists_eq_right, and_self]
--     · rintro e he f hf heq
--       simpa [he, ↓reduceDIte, hf] using heq
--     · rintro s ⟨hdiag, e, he, rfl⟩
--       use e, he, by simp [he]

lemma simplify_idOn_simpleCanonical {G : Graph α (Sym2 α)} [H : G.SimpleCanonical] :
    G.simplify = G := by
  refine Graph.ext rfl fun e x y ↦ ?_
  induction' e with u v
  rw [simplify_isLink]
  refine ⟨fun ⟨hne, ⟨e, B⟩, C⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [C, isLink_iff_mem_edgeSet]
    rw [isLink_iff_eq] at B
    exact mem_of_mem_inter_right B
  · rw [isLink_iff_eq] at h
    obtain ⟨h, h'⟩ := h
    refine ⟨?_, ?_, h⟩
    · rintro rfl
      refine H.loopless x ⟨s(x, x), ?_⟩
      rwa [isLink_iff_mem_edgeSet]
    · rw [← isLink_iff_mem_edgeSet] at h'
      exact ⟨s(x, y), h'⟩

lemma SimpleCanonical.of_le {G H : Graph α (Sym2 α)} [G.SimpleCanonical] (hle : H ≤ G) :
    H.SimpleCanonical where
  toSimple := Simple.of_le hle
  canonical e he := by
    nth_rw 2 [← SimpleCanonical.canonical e (edgeSet_subset_of_le hle he)]
    rw [toSym2_eq_of_le hle he]

universe u v

lemma forall_Simplify {α : Type u} {β : Type v} (F : ∀ {β : Type u}, Graph α β → Prop)
    (F' : ∀ {β : Type v}, Graph α β → Prop) [hF : GraphicVertexFunction F' F]
    (h : ∀ (G' : Graph α (Sym2 α)) [G'.SimpleCanonical], F G') :
    ∀ (G : Graph α β) [G.Simple], F' G := fun G hG => by
    classical
    by_cases hα : Nonempty α
    · rw [hF.invariant simplify_vertexIsom]
      exact h G.simplify
    · rw [not_nonempty_iff] at hα
      rw [eq_bot_of_isEmpty (G := G)]
      refine (hF.invariant ?_) ▸ (h _ : F (⊥ : Graph α (Sym2 α)))
      obtain ⟨F⟩ := bot_hasIsom_bot
      use F
      ext ⟨x, hx⟩
      simp at hx

end Graph
