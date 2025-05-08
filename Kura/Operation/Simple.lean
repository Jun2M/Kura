import Kura.Operation.Hom


open Set Function
variable {α ε α' α'' ε' : Type*} {G G' H H' : Graph α ε} {u v w : α} {e f : ε} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set ε}


class Graph.IsLoopless (G : Graph α ε) : Prop where
  loopless x : ¬ G.Adj x x

lemma Graph.IsLoopless.of_le {G H : Graph α ε} [G.IsLoopless] (hle : H ≤ G) : H.IsLoopless where
  loopless x := by
    rintro ⟨e, hbtw⟩
    exact IsLoopless.loopless x ⟨e, hbtw.of_le hle⟩

instance Graph.instLooplessGraphic : Graph.GraphicFunction IsLoopless where
  presv_isom G G' h := by
    ext
    obtain ⟨g, hg⟩ := h.symm
    obtain ⟨f, hf⟩ := h
    refine ⟨fun hloop ↦ ⟨fun x ⟨e, hbtw⟩ ↦ ?_⟩, fun hloop ↦ ⟨fun x ⟨e, hbtw⟩ ↦ ?_⟩⟩
    · exact hloop.loopless (g x) ⟨g.edgeFun e, hbtw.isIsomOn hg hbtw.edge_mem hbtw.vx_mem_left hbtw.vx_mem_right⟩
    · exact hloop.loopless (f x) ⟨f.edgeFun e, hbtw.isIsomOn hf hbtw.edge_mem hbtw.vx_mem_left hbtw.vx_mem_right⟩

lemma Graph.Inc₂.ne [hG : G.IsLoopless] (hbtw : G.Inc₂ e u v) : u ≠ v := by
  rintro rfl
  exact hG.loopless u ⟨e, hbtw⟩

@[simp]
lemma Graph.toSym2_not_isDiag {G : Graph α ε} [G.IsLoopless] {e : ε} {he : e ∈ G.E} :
    ¬ (G.toSym2 e he).IsDiag := by
  obtain ⟨x, y, hxy⟩ := exists_inc₂_of_mem_edgeSet he
  have := hxy.ne
  rwa [(toSym2_eq_pair_iff hxy.edge_mem).mpr hxy]

class Graph.IsSimple (G : Graph α ε) : Prop extends IsLoopless G where
  no_multi_edges e f he hf : G.toSym2 e he = G.toSym2 f hf → e = f

lemma Graph.IsSimple.of_le {G H : Graph α ε} [G.IsSimple] (hle : H ≤ G) : H.IsSimple where
  loopless x := by
    rintro ⟨e, hbtw⟩
    exact IsLoopless.loopless x ⟨e, hbtw.of_le hle⟩
  no_multi_edges e f he hf h := by
    obtain ⟨x, y, hxy⟩ := exists_inc₂_of_mem_edgeSet he
    rw [← toSym2_eq_pair_iff he] at hxy
    rw [hxy, eq_comm, toSym2_eq_of_le hle hf] at h
    rw [toSym2_eq_of_le hle he] at hxy
    refine IsSimple.no_multi_edges e f (edgeSet_subset_of_le hle he) (edgeSet_subset_of_le hle hf) ?_
    rw [h, hxy]

@[simp]
lemma Graph.toSym2_inj [hG : G.IsSimple] (he : e ∈ G.E) (hf : f ∈ G.E) :
    G.toSym2 e he = G.toSym2 f hf ↔ e = f :=
  ⟨fun h ↦ hG.no_multi_edges e f he hf h, fun h ↦ h ▸ rfl⟩

@[simp]
lemma Graph.Inc₂.edge_eq_iff_inc₂ [hG : G.IsSimple] (hbtw : G.Inc₂ e u v) :
    G.Inc₂ f u v ↔ e = f := by
  refine ⟨fun h ↦ ?_, (· ▸ hbtw)⟩
  obtain a := ((toSym2_eq_pair_iff hbtw.edge_mem).mpr hbtw).trans ((toSym2_eq_pair_iff h.edge_mem).mpr h).symm
  exact hG.no_multi_edges e f hbtw.edge_mem h.edge_mem a

@[mk_iff]
class Graph.IsSimpleCanonical (G : Graph α (Sym2 α)) : Prop extends IsSimple G where
  canonical e he : G.toSym2 e he = e

@[simp]
lemma Graph.toSym2_eq_self {G : Graph α (Sym2 α)} [G.IsSimpleCanonical] {e : Sym2 α} {he : e ∈ G.E} :
    G.toSym2 e he = e := IsSimpleCanonical.canonical e he

@[simp]
lemma Graph.inc₂_iff_mem_edgeSet {G : Graph α (Sym2 α)} [G.IsSimpleCanonical] :
    G.Inc₂ s(u, v) u v ↔ s(u, v) ∈ G.E := by
  refine ⟨Inc₂.edge_mem, fun h ↦ ?_⟩
  rw [← toSym2_eq_pair_iff h]
  exact IsSimpleCanonical.canonical s(u, v) h

@[simp]
lemma Graph.inc₂_iff_eq {G : Graph α (Sym2 α)} [G.IsSimpleCanonical] {e : Sym2 α} :
    G.Inc₂ e u v ↔ e = s(u, v) ∧ s(u, v) ∈ G.E := by
  refine ⟨fun h ↦ ?_, fun ⟨he, h⟩ ↦ he ▸ inc₂_iff_mem_edgeSet.mpr h⟩
  induction' e with x y
  have hxy := h.edge_mem
  rw [← toSym2_eq_pair_iff h.edge_mem, IsSimpleCanonical.canonical s(x, y)] at h
  exact ⟨h, h ▸ hxy⟩

#print Graph.Homsys.IsHomOn.toSym2

instance Graph.instSimpleGraphic : Graph.GraphicFunction IsSimple where
  presv_isom G G' h := by
    ext
    refine ⟨fun hsimple ↦ ?_, fun hsimple ↦ ?_⟩
    · exact {
        loopless := (instLooplessGraphic.presv_isom G G' h ▸ hsimple.toIsLoopless).loopless
        no_multi_edges := fun e f he hf heq ↦ by
          obtain ⟨f, hf⟩ := h.symm
          sorry}
    · exact {
        loopless := (instLooplessGraphic.presv_isom G G' h ▸ hsimple.toIsLoopless).loopless
        no_multi_edges := fun e f he hf h ↦ by
          sorry}

/-- The graph induced by a simple graph -/
@[simps]
def SimpleGraph.toGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  V := univ
  E := G.edgeSet
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
def toSimpleGraph (G : Graph α ε) : SimpleGraph G.V where
  Adj a b := a ≠ b ∧ G.Adj a b
  symm a b hab := by simpa only [ne_eq, eq_comm, adj_comm] using hab

@[simps! vxSet]
def Simplify (G : Graph α ε) : Graph α (Sym2 α) :=
  oftoSym2 G.V {s | ¬ s.IsDiag ∧ ∃ (e : ε) (he : e ∈ G.E), G.toSym2 e he = s}
    (fun e _ ↦ e) (fun e x ⟨f, hf, h, hdiag⟩ hx ↦ by subst e; exact vx_mem_of_toSym2 hx)

-- @[simps! vxSet edgeSet]
-- def Simplify (G : Graph α ε) : Graph α (Sym2 α) :=
--   oftoSym2 G.V {s | ∃ u v, s(u, v) = s ∧ u ≠ v ∧ G.Adj u v}
--     (fun e _ ↦ e) (fun e x ⟨u, v, h, hne, hadj⟩ hx ↦ by
--     subst e
--     simp at hx
--     obtain (rfl | rfl) := hx
--     · exact hadj.mem_left
--     · exact hadj.mem_right)

lemma Simplify_edgeSet : G.Simplify.E = {s | ¬s.IsDiag ∧ ∃ x, ∃ (x_1 : x ∈ G.E), G.toSym2 x x_1 = s} := by
  unfold Simplify
  simp only [mem_setOf_eq, oftoSym2_edgeSet, exists_and_right]

@[simp]
lemma simplify_edgeSet_adj {G : Graph α ε} : (G.Simplify).E = {s | ∃ u v, s(u, v) = s ∧ u ≠ v ∧ G.Adj u v} := by
  ext s
  simp only [Simplify, mem_setOf_eq, oftoSym2_edgeSet, exists_and_right, ← ne_eq]
  constructor
  · rintro ⟨hdiag, e, he, hs⟩
    induction' s with x y
    use x, y, rfl, hdiag, e, by rwa [toSym2_eq_pair_iff] at hs
  · rintro ⟨u, v, rfl, hdiag, e, hbtw⟩
    exact ⟨hdiag, e, hbtw.edge_mem, hbtw.toSym2⟩

@[simp]
lemma simplify_inc₂ {G : Graph α ε} (e : Sym2 α) (x y : α) :
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
lemma simplify_toSym2 {G : Graph α ε} {e : Sym2 α} (he : e ∈ (Simplify G).E) :
    (Simplify G).toSym2 e he = e := by
  induction' e with x y
  simp only [Simplify_edgeSet, mem_setOf_eq, toSym2_eq_pair_iff, simplify_inc₂, ne_eq,
    and_true] at he ⊢
  obtain ⟨hdiag, e, he, h⟩ := he
  exact ⟨hdiag, e, h⟩

instance instSimpleCanonicalSimplify : IsSimpleCanonical (Simplify G) where
  loopless x := by
    simp only [Adj, Simplify, mem_setOf_eq, oftoSym2_inc₂, exists_prop, exists_eq_right,
      Sym2.isDiag_iff_proj_eq, not_true_eq_false, toSym2_eq_pair_iff, false_and, not_false_eq_true]
  no_multi_edges e f he hf h := by simpa only [Simplify, mem_setOf_eq, oftoSym2_tosym2] using h
  canonical e he := by simp only [Simplify, mem_setOf_eq, oftoSym2_tosym2]

lemma simplify_isom [hα : Nonempty α] {G : Graph α ε} [hG : G.IsSimple] : G ≤↔ G.Simplify := by
  classical
  refine ⟨⟨id, fun e ↦ if he : e ∈ G.E then G.toSym2 e he else s(hα.some, hα.some)⟩, ⟨?_, ?_, ?_⟩⟩
  · refine {
      Mapsto_vx := fun x ↦ by simp,
      inc₂ := fun e x y hxy ↦ by
        simp only [hxy.edge_mem, ↓reduceDIte, id_eq, simplify_inc₂, toSym2_eq_pair_iff]
        use hxy.ne, ⟨e, hxy⟩}
  · rw [Simplify_vxSet]
    exact bijOn_id G.V
  · rw [Simplify_edgeSet]
    refine ⟨?_, ?_, ?_⟩
    · rintro e he
      simp only [he, ↓reduceDIte, mem_setOf_eq, toSym2_not_isDiag, not_false_eq_true, true_and]
      use e, he
    · rintro e he f hf heq
      simp only [he, ↓reduceDIte, hf] at heq
      rwa [toSym2_inj] at heq
    · rintro s ⟨hdiag, e, he, rfl⟩
      use e, he, by simp [he]

lemma simplify_vertexIsom [hα : Nonempty α] {G : Graph α ε} [hG : G.IsSimple] :
    ∃ f : ε → Sym2 α, (HomSys.ofEdgeFun f).IsIsomOn G G.Simplify := by
  classical
  refine ⟨fun e ↦ if he : e ∈ G.E then G.toSym2 e he else s(hα.some, hα.some), ⟨?_, ?_, ?_⟩⟩
  · refine {
      Mapsto_vx := fun x ↦ by simp,
      inc₂ := fun e x y hxy ↦ by
        simp only [HomSys.ofEdgeFun_edgeFun, hxy.edge_mem, ↓reduceDIte, HomSys.ofEdgeFun_toFun,
          id_eq, inc₂_iff_eq, toSym2_eq_pair_iff, hxy, simplify_edgeSet_adj, mem_setOf_eq, true_and]
        use x, y, rfl, hxy.ne, e, hxy}
  · rw [Simplify_vxSet]
    exact bijOn_id G.V
  · rw [Simplify_edgeSet]
    refine ⟨?_, ?_, ?_⟩
    · rintro e he
      simp only [HomSys.ofEdgeFun_edgeFun, he, ↓reduceDIte, mem_setOf_eq, toSym2_not_isDiag,
        not_false_eq_true, toSym2_inj, exists_prop, exists_eq_right, and_self]
    · rintro e he f hf heq
      simpa [he, ↓reduceDIte, hf] using heq
    · rintro s ⟨hdiag, e, he, rfl⟩
      use e, he, by simp [he]

lemma simplify_idOn_simpleCanonical {G : Graph α (Sym2 α)} [H : G.IsSimpleCanonical] :
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

lemma IsSimpleCanonical.of_le {G H : Graph α (Sym2 α)} [G.IsSimpleCanonical] (hle : H ≤ G) :
    H.IsSimpleCanonical where
  toIsSimple := IsSimple.of_le hle
  canonical e he := by
    nth_rw 2 [← IsSimpleCanonical.canonical e (edgeSet_subset_of_le hle he)]
    rw [toSym2_eq_of_le hle he]

lemma forall_Simplify {ε : Type u_1} (F : {ε : Type u_1} → Graph α ε → Prop)
    [hF : GraphicVertexFunction F] [Nonempty α] [Nonempty ε] [Nonempty (Sym2 α)]
    (h : ∀ (G' : Graph α (Sym2 α)) [G'.IsSimple], (∀ (e) (he : e ∈ G'.E), G'.toSym2 e he = e) → F G') :
    ∀ (G : Graph α ε) [G.IsSimple], F G := fun G hG => by
    rw [hF.presv_isom G G.Simplify simplify_vertexIsom]
    exact h G.Simplify fun e he ↦ simplify_toSym2 he

end Graph
