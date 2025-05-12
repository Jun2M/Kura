import Kura.Operation.Hom2


open Set Function Graph
variable {α β α' α'' β' : Type*} {G G' H H' : Graph α β} {u v w : α} {e f : β} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set β}


class Graph.IsLoopless (G : Graph α β) : Prop where
  loopless x : ¬ G.Adj x x

lemma Graph.IsLoopless.of_le {G H : Graph α β} [G.IsLoopless] (hle : H ≤ G) : H.IsLoopless where
  loopless x := by
    rintro ⟨e, hbtw⟩
    exact IsLoopless.loopless x ⟨e, hbtw.of_le hle⟩

instance Graph.instLooplessGraphic : Graph.GraphicFunction IsLoopless IsLoopless where
  invariant h := by
    ext
    obtain ⟨g⟩ := h.symm
    obtain ⟨f⟩ := h
    refine ⟨fun hloop ↦ ⟨fun x ⟨e, hbtw⟩ ↦ ?_⟩, fun hloop ↦ ⟨fun x ⟨e, hbtw⟩ ↦ ?_⟩⟩
    · exact hloop.loopless (g.toFun ⟨x, hbtw.vx_mem_right⟩) ⟨g.edgeFun ⟨e, hbtw.edge_mem⟩, hbtw.isIsomOn g⟩
    · exact hloop.loopless (f.toFun ⟨x, hbtw.vx_mem_right⟩) ⟨f.edgeFun ⟨e, hbtw.edge_mem⟩, hbtw.isIsomOn f⟩

lemma Graph.Inc₂.ne [hG : G.IsLoopless] (hbtw : G.Inc₂ e u v) : u ≠ v := by
  rintro rfl
  exact hG.loopless u ⟨e, hbtw⟩

@[simp]
lemma Graph.toSym2_not_isDiag {G : Graph α β} [G.IsLoopless] {e : β} {he : e ∈ E(G)} :
    ¬ (G.toSym2 e he).IsDiag := by
  obtain ⟨x, y, hxy⟩ := exists_inc₂_of_mem_edgeSet he
  have := hxy.ne
  rwa [(toSym2_eq_pair_iff hxy.edge_mem).mpr hxy]

class Graph.Simple (G : Graph α β) : Prop extends IsLoopless G where
  no_multi_edges e f he hf : G.toSym2 e he = G.toSym2 f hf → e = f

lemma Graph.Simple.of_le {G H : Graph α β} [G.Simple] (hle : H ≤ G) : H.Simple where
  loopless x := by
    rintro ⟨e, hbtw⟩
    exact IsLoopless.loopless x ⟨e, hbtw.of_le hle⟩
  no_multi_edges e f he hf h := by
    obtain ⟨x, y, hxy⟩ := exists_inc₂_of_mem_edgeSet he
    rw [← toSym2_eq_pair_iff he] at hxy
    rw [hxy, eq_comm, toSym2_eq_of_le hle hf] at h
    rw [toSym2_eq_of_le hle he] at hxy
    refine Simple.no_multi_edges e f (edgeSet_subset_of_le hle he) (edgeSet_subset_of_le hle hf) ?_
    rw [h, hxy]

@[simp]
lemma Graph.toSym2_inj [hG : G.Simple] (he : e ∈ E(G)) (hf : f ∈ E(G)) :
    G.toSym2 e he = G.toSym2 f hf ↔ e = f :=
  ⟨fun h ↦ hG.no_multi_edges e f he hf h, fun h ↦ h ▸ rfl⟩

@[simp]
lemma Graph.Inc₂.edge_eq_iff_inc₂ [hG : G.Simple] (hbtw : G.Inc₂ e u v) :
    G.Inc₂ f u v ↔ e = f := by
  refine ⟨fun h ↦ ?_, (· ▸ hbtw)⟩
  obtain a := ((toSym2_eq_pair_iff hbtw.edge_mem).mpr hbtw).trans ((toSym2_eq_pair_iff h.edge_mem).mpr h).symm
  exact hG.no_multi_edges e f hbtw.edge_mem h.edge_mem a

@[simp]
lemma not_simple_iff : ¬ G.Simple ↔ (∃ x, G.Adj x x) ∨ ∃ e f he hf, G.toSym2 e he = G.toSym2 f hf ∧ e ≠ f := by
  refine ⟨fun h ↦ ?_, fun h hsimp ↦ ?_⟩
  · contrapose! h
    exact {loopless := h.1, no_multi_edges := h.2}
  · obtain ⟨x, hadj⟩ | ⟨e, f, he, hf, heq, hne⟩ := h
    · exact hsimp.loopless x hadj
    · exact hne <| hsimp.no_multi_edges e f he hf heq

@[mk_iff]
class Graph.SimpleCanonical (G : Graph α (Sym2 α)) : Prop extends Simple G where
  canonical e he : G.toSym2 e he = e

instance Graph.instBotSimpleCanonical : SimpleCanonical (⊥ : Graph α (Sym2 α)) where
  loopless x := not_adj_of_right_not_mem_vertexSet x fun a ↦ a
  no_multi_edges e f he hf h := by simp at he
  canonical e he := by simp at he

instance Graph.instNoEdgeSimpleCanonical : SimpleCanonical (Graph.noEdge S (Sym2 α)) where
  loopless x := not_adj_noEdge
  no_multi_edges e f he hf h := by simp at he
  canonical e he := by simp at he

@[simp]
lemma Graph.toSym2_eq_self {G : Graph α (Sym2 α)} [G.SimpleCanonical] {e : Sym2 α} {he : e ∈ E(G)} :
    G.toSym2 e he = e := SimpleCanonical.canonical e he

@[simp]
lemma Graph.inc₂_iff_mem_edgeSet {G : Graph α (Sym2 α)} [G.SimpleCanonical] :
    G.Inc₂ s(u, v) u v ↔ s(u, v) ∈ E(G) := by
  refine ⟨Inc₂.edge_mem, fun h ↦ ?_⟩
  rw [← toSym2_eq_pair_iff h]
  exact SimpleCanonical.canonical s(u, v) h

@[simp]
lemma Graph.inc₂_iff_eq {G : Graph α (Sym2 α)} [G.SimpleCanonical] {e : Sym2 α} :
    G.Inc₂ e u v ↔ e = s(u, v) ∧ s(u, v) ∈ E(G) := by
  refine ⟨fun h ↦ ?_, fun ⟨he, h⟩ ↦ he ▸ inc₂_iff_mem_edgeSet.mpr h⟩
  induction' e with x y
  have hxy := h.edge_mem
  rw [← toSym2_eq_pair_iff h.edge_mem, SimpleCanonical.canonical s(x, y)] at h
  exact ⟨h, h ▸ hxy⟩


instance Graph.instSimpleGraphic : Graph.GraphicFunction Simple Simple where
  invariant h := by
    ext
    refine ⟨fun hsimple ↦ ?_, fun hsimple ↦ ?_⟩
    · exact {
        loopless := (instLooplessGraphic.invariant h ▸ hsimple.toIsLoopless).loopless
        no_multi_edges := fun e f he hf heq ↦ by
          obtain ⟨f, hf⟩ := h.symm
          sorry}
    · exact {
        loopless := (instLooplessGraphic.invariant h ▸ hsimple.toIsLoopless).loopless
        no_multi_edges := fun e f he hf h ↦ by
          sorry}

/-- The graph induced by a simple graph -/
@[simps]
def SimpleGraph.toGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  vertexSet := univ
  edgeSet := G.edgeSet
  Inc₂ e x y := s(x,y) = e ∧ G.Adj x y
  inc₂_symm e x y := by simp [Sym2.eq_swap, SimpleGraph.adj_comm]
  vx_mem_left_of_inc₂ e x y := by simp
  edge_mem_iff_exists_inc₂ e := by
    refine ⟨fun he ↦ ?_, fun ⟨x, y, hx, he⟩ ↦ by simp [he, ← hx]⟩
    induction' e with x y
    use x, y
    simpa using he
  eq_or_eq_of_inc₂_of_inc₂ a b c d e h1 h2 := by
    obtain ⟨rfl, he⟩ := h1
    obtain ⟨heq, he'⟩ := h2
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
    tauto

variable {G' H' : SimpleGraph α}

@[simp]
lemma SimpleGraph.toGraph_adj : (SimpleGraph.toGraph G').Adj = G'.Adj := by
  ext x y
  simp_rw [Graph.Adj, toGraph_inc₂, exists_eq_left']

@[simp]
lemma SimpleGraph.toGraph_inj : G'.toGraph = H'.toGraph ↔ G' = H' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  ext x y
  rw [← toGraph_adj, ← toGraph_adj, h]

namespace Graph

@[simps]
def toSimpleGraph (G : Graph α β) : SimpleGraph V(G) where
  Adj a b := a ≠ b ∧ G.Adj a b
  symm a b hab := by simpa only [ne_eq, eq_comm, adj_comm] using hab

@[simps! vertexSet]
def Simplify (G : Graph α β) : Graph α (Sym2 α) :=
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

instance instSimplifyVxSetFinite (G : Graph α β) [Finite V(G)] : Finite V(G.Simplify) := by
  rw [Simplify_vertexSet]
  infer_instance

@[simp]
lemma Simplify_edgeSet : E(G.Simplify) = {s | ¬s.IsDiag ∧ ∃ x, ∃ (x_1 : x ∈ E(G)), G.toSym2 x x_1 = s} := by
  unfold Simplify
  simp only [mem_setOf_eq, oftoSym2_edgeSet, exists_and_right]

lemma simplify_edgeSet_subset_image_toSym2 :
    E(G.Simplify) ⊆ Set.range (fun a ↦ G.toSym2 a.1 a.2 : E(G) → _) := by
  rintro s hs
  simp only [Simplify_edgeSet, mem_setOf_eq] at hs
  obtain ⟨hdiag, e, he, rfl⟩ := hs
  use ⟨e, he⟩

lemma card_simplify_edgeSet_le (G : Graph α β) [Finite E(G)] :
    E(G.Simplify).ncard ≤ E(G).ncard := by
  refine le_trans ?_ <| Finite.card_range_le (fun a ↦ G.toSym2 a.1 a.2)
  rw [Set.Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard simplify_edgeSet_subset_image_toSym2

instance instSimplifyFinite (G : Graph α β) [Finite E(G)] : Finite E(G.Simplify) :=
  Set.finite_range (fun a ↦ G.toSym2 a.1 a.2 : E(G) → _)
  |>.subset simplify_edgeSet_subset_image_toSym2

lemma simplify_edgeSet_adj {G : Graph α β} : E(G.Simplify) = {s | ∃ u v, s(u, v) = s ∧ u ≠ v ∧ G.Adj u v} := by
  ext s
  simp only [Simplify, mem_setOf_eq, oftoSym2_edgeSet, exists_and_right, ← ne_eq]
  constructor
  · rintro ⟨hdiag, e, he, hs⟩
    induction' s with x y
    use x, y, rfl, hdiag, e, by rwa [toSym2_eq_pair_iff] at hs
  · rintro ⟨u, v, rfl, hdiag, e, hbtw⟩
    exact ⟨hdiag, e, hbtw.edge_mem, hbtw.toSym2⟩

@[simp]
lemma simplify_inc₂ {G : Graph α β} (e : Sym2 α) (x y : α) :
    G.Simplify.Inc₂ e x y ↔ x ≠ y ∧ G.Adj x y ∧ e = s(x, y) := by
  simp only [Simplify, mem_setOf_eq, oftoSym2_inc₂, exists_and_right, exists_prop, ne_eq]
  rw [← and_assoc (a := x ≠ y), and_congr_left_iff]
  rintro rfl
  simp only [toSym2_eq_pair_iff, exists_prop, Sym2.isDiag_iff_proj_eq, Adj, ne_eq,
    and_congr_right_iff]
  rintro hne
  refine ⟨fun ⟨e, he, hbtw⟩ ↦ ?_, fun ⟨e, hbtw⟩ ↦ ?_⟩
  · use e
  · use e, hbtw.edge_mem

@[simp]
lemma simplify_adj : (Simplify G).Adj u v ↔ u ≠ v ∧ G.Adj u v := by
  simp only [Adj, Simplify, mem_setOf_eq, oftoSym2_inc₂, exists_and_right, exists_prop,
    exists_eq_right, toSym2_eq_pair_iff, Sym2.isDiag_iff_proj_eq, ← ne_eq]
  rw [and_congr_right_iff]
  exact fun hne ↦ exists_congr fun e ↦ and_iff_right_iff_imp.mpr (Inc₂.edge_mem ·)

@[simp]
lemma simplify_toSym2 {G : Graph α β} {e : Sym2 α} (he : e ∈ E(Simplify G)) :
    (Simplify G).toSym2 e he = e := by
  induction' e with x y
  simp only [Simplify_edgeSet, mem_setOf_eq, toSym2_eq_pair_iff, simplify_inc₂, ne_eq,
    and_true] at he ⊢
  obtain ⟨hdiag, e, he, h⟩ := he
  exact ⟨hdiag, e, h⟩

instance instSimpleCanonicalSimplify : SimpleCanonical (Simplify G) where
  loopless x := by
    simp only [Adj, Simplify, mem_setOf_eq, oftoSym2_inc₂, exists_prop, exists_eq_right,
      Sym2.isDiag_iff_proj_eq, not_true_eq_false, toSym2_eq_pair_iff, false_and, not_false_eq_true]
  no_multi_edges e f he hf h := by simpa only [Simplify, mem_setOf_eq, oftoSym2_tosym2] using h
  canonical e he := by simp only [Simplify, mem_setOf_eq, oftoSym2_tosym2]

lemma simplify_edgeSet_ncard_le (G : Graph α β) [hE : Finite E(G)] :
    E(G.Simplify).ncard ≤ E(G).ncard := by
  rw [Simplify_edgeSet]
  have : Finite ↑{e | ∃ (he : e ∈ E(G)), ¬(G.toSym2 e he).IsDiag} := by
    apply Set.Finite.subset hE
    rintro e he
    exact he.1
  refine le_trans ?_ (Set.ncard_le_ncard (ht := hE) (fun e he ↦ he.choose) : {e | ∃ (he : e ∈ E(G)), ¬ (G.toSym2 e he).IsDiag}.ncard ≤ _)
  apply Nat.card_le_card_of_surjective (fun e ↦ ⟨G.toSym2 e e.prop.choose, by
    use e.prop.choose_spec, e, e.prop.choose⟩)
  rintro ⟨e, hne, f, hf, rfl⟩
  simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq, Subtype.exists]
  use f, ⟨hf, hne⟩

lemma simplify_hasIsom [hG : G.Simple] : G ↔ᴳ G.Simplify := ⟨{
  toFun := id
  edgeFun e := ⟨G.toSym2 e e.prop, by
    rw [Simplify_edgeSet]
    simp only [mem_setOf_eq, toSym2_not_isDiag, not_false_eq_true, toSym2_inj, exists_prop,
      exists_eq_right, Subtype.coe_prop, and_self]⟩
  inc₂ e x y hbtw := by
    simp only [Simplify_vertexSet, id_eq, inc₂_iff_eq, toSym2_eq_pair_iff, hbtw,
      simplify_edgeSet_adj, ne_eq, mem_setOf_eq, true_and]
    use x, y, rfl, hbtw.ne, e, hbtw
  invFun := id
  vx_left_inv := congrFun rfl
  vx_right_inv := congrFun rfl
  edgeInvFun e := by
    obtain he := by simpa only [Simplify_edgeSet, ne_eq, mem_setOf_eq] using e.prop
    use he.2.choose, he.2.choose_spec.choose
  edge_left_inv e := by
    have : G.toSym2 ↑e e.prop ∈ E(G.Simplify) := by
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

lemma simplify_eq_edgeMap [hα : Nonempty α] [hG : G.Simple] [DecidablePred (· ∈ E(G))] :
    G.Simplify = G.edgeMap (fun e ↦ if he : e ∈ E(G) then G.toSym2 e he else s(hα.some, hα.some))
    (fun e he f hf => by simp [he, hf]) := by
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
    rw [eq_comm, toSym2_eq_pair_iff, edgeMap_inc₂]
    use f, by simp [hf]
    rw [← toSym2_eq_pair_iff hf, ← Sym2.eq_mk_out]

lemma simplify_vertexIsom [hα : Nonempty α] [hG : G.Simple] :
    ∃ (f : β → Sym2 α) (hf : InjOn f E(G)), G.edgeMap f hf = G.Simplify := by
  classical
  use (fun e => if he : e ∈ E(G) then G.toSym2 e he else s(hα.some, hα.some)),
    (fun e he f hf => by simp [he, hf]), simplify_eq_edgeMap.symm

lemma simplify_edgeSet_ncard_lt (G : Graph α β) [hE : Finite E(G)] :
    E(G.Simplify).ncard < E(G).ncard ↔ ¬ G.Simple := by
  refine ⟨fun hG hsimp ↦ ?_, fun hsimp ↦ ?_⟩
  · simp [(simplify_hasIsom (hG := hsimp)).eq (·.edgeSet.ncard) (·.edgeSet.ncard)] at hG
  · rw [not_simple_iff] at hsimp
    obtain ⟨x, e, hinc⟩ | ⟨e, f, he, hf, heq, hne⟩ := hsimp
    · sorry
    · sorry

-- lemma simplify_vertexIsom [Nonempty α] [hG : G.Simple] :
--     ∃ f : β → Sym2 α, (Funs.ofEdgeFun f).IsIsomOn G G.Simplify := by
--   classical
--   refine ⟨fun e ↦ if he : e ∈ E(G) then G.toSym2 e he else s(hα.some, hα.some), ⟨?_, ?_, ?_⟩⟩
--   · refine {
--       Mapsto_vx := fun x ↦ by simp,
--       inc₂ := fun e x y hxy ↦ by
--         simp only [HomSys.ofEdgeFun_edgeFun, hxy.edge_mem, ↓reduceDIte, HomSys.ofEdgeFun_toFun,
--           id_eq, inc₂_iff_eq, toSym2_eq_pair_iff, hxy, simplify_edgeSet_adj, mem_setOf_eq, true_and]
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
    G.Simplify = G := by
  refine Graph.ext rfl fun e x y ↦ ?_
  induction' e with u v
  rw [simplify_inc₂]
  refine ⟨fun ⟨hne, ⟨e, B⟩, C⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [C, inc₂_iff_mem_edgeSet]
    rw [inc₂_iff_eq] at B
    exact mem_of_mem_inter_right B
  · rw [inc₂_iff_eq] at h
    obtain ⟨h, h'⟩ := h
    refine ⟨?_, ?_, h⟩
    · rintro rfl
      refine H.loopless x ⟨s(x, x), ?_⟩
      rwa [inc₂_iff_mem_edgeSet]
    · rw [← inc₂_iff_mem_edgeSet] at h'
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
      exact h G.Simplify
    · simp at hα
      rw [eq_bot_of_isEmpty (G := G)]
      sorry

end Graph
