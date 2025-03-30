import Kura.Basic


open Set Function
variable {α β : Type*} {G G₁ G₂ : Graph α β} {u v w x y : α} {e f g : β}
namespace Graph


/-- Subgraph order of Graph -/
instance instPartialOrderGraph : PartialOrder (Graph α β) where
  le G₁ G₂ := G₁.V ⊆ G₂.V ∧ G₁.E ⊆ G₂.E ∧ ∀ v e (hin : e ∈ G₁.E),
    G₁.Inc v e ↔ G₂.Inc v e
  le_refl G := by simp only [subset_refl, le_refl, implies_true, exists_const, and_self]
  le_trans G₁ G₂ G₃ h₁₂ h₂₃ := by
    obtain ⟨h₁₂v, h₁₂e, h₁₂S⟩ := h₁₂
    obtain ⟨h₂₃v, h₂₃e, h₂₃S⟩ := h₂₃
    refine ⟨h₁₂v.trans h₂₃v, h₁₂e.trans h₂₃e, ?_⟩
    rintro v e hin
    rw [h₁₂S _ _ hin, h₂₃S _ _ (h₁₂e hin)]
  le_antisymm G₁ G₂ h₁₂ h₂₁ := by
    ext1
    · exact h₁₂.1.antisymm h₂₁.1
    · exact h₁₂.2.1.antisymm h₂₁.2.1
    · rename_i v e
      by_cases h : e ∈ G₁.E
      · rw [h₁₂.2.2 _ _ h]
      · constructor <;> intro hInc <;> exfalso
        · exact h <| G₁.edge_mem_of_inc hInc
        · exact h <| (h₁₂.2.1.antisymm h₂₁.2.1) ▸ (G₂.edge_mem_of_inc hInc)

@[simp]
lemma vx_subset_of_le (hle : G₁ ≤ G₂) : G₁.V ⊆ G₂.V := hle.1

@[simp]
lemma mem_of_le (hle : G₁ ≤ G₂) : x ∈ G₁.V → x ∈ G₂.V := (hle.1 ·)

@[simp]
lemma edge_subset_of_le (hle : G₁ ≤ G₂) : G₁.E ⊆ G₂.E := hle.2.1

@[simp]
lemma edge_mem_of_le (hle : G₁ ≤ G₂) : e ∈ G₁.E → e ∈ G₂.E := (hle.2.1 ·)

lemma Inc_iff_Inc_of_edge_mem_le (hle : G₁ ≤ G₂) (he : e ∈ G₁.E) : G₁.Inc v e ↔ G₂.Inc v e :=
  hle.2.2 _ _ he

@[simp]
lemma Inc.le (hinc : G₁.Inc x e) (hle : G₁ ≤ G₂) : G₂.Inc x e := by
  rwa [← hle.2.2 _ _ hinc.edge_mem]

lemma IsLoop_iff_IsLoop_of_edge_mem_le (hle : G₁ ≤ G₂) (he : e ∈ G₁.E) :
    G₁.IsLoop e ↔ G₂.IsLoop e := by
  constructor <;> rintro ⟨v, hinc, heq⟩
  · use v, (Inc_iff_Inc_of_edge_mem_le hle he).mp hinc
    intro y hy
    refine heq y ?_
    beta_reduce
    rwa [Inc_iff_Inc_of_edge_mem_le hle hinc.edge_mem]
  · use v, (Inc_iff_Inc_of_edge_mem_le hle he).mpr hinc
    intro y hy
    refine heq y ?_
    beta_reduce
    rwa [← Inc_iff_Inc_of_edge_mem_le hle he]

lemma IsLoop.le (hisLoop : G₁.IsLoop e) (hle : G₁ ≤ G₂) : G₂.IsLoop e := by
  rwa [← IsLoop_iff_IsLoop_of_edge_mem_le hle hisLoop.mem]

lemma IsBetween_iff_IsBetween_of_edge_mem_le (hle : G₁ ≤ G₂) (he : e ∈ G₁.E) :
    G₁.IsBetween e u v ↔ G₂.IsBetween e u v := by
  constructor <;> rintro ⟨hincu, hincv, hLoop⟩
  · use hincu.le hle, hincv.le hle
    rwa [← IsLoop_iff_IsLoop_of_edge_mem_le hle he]
  · refine ⟨?_, ?_, ?_⟩
    on_goal 3 => rwa [IsLoop_iff_IsLoop_of_edge_mem_le hle he]
    all_goals
      simp_rw [Inc_iff_Inc_of_edge_mem_le hle he]
      assumption

lemma IsBetween.le (h : G₁.IsBetween e u v) (hle : G₁ ≤ G₂) : G₂.IsBetween e u v := by
  rwa [← IsBetween_iff_IsBetween_of_edge_mem_le hle (edge_mem h)]

lemma Adj.le (hadj : G₁.Adj u v) (hle : G₁ ≤ G₂) : G₂.Adj u v := by
  obtain ⟨e, hincu, hincv, hLoop⟩ := hadj
  use e, hincu.le hle, hincv.le hle
  exact fun a ↦ (hLoop a).le hle

lemma reflAdj.le (h : G₁.reflAdj u w) (hle : G₁ ≤ G₂) : G₂.reflAdj u w := by
  obtain hadj | ⟨rfl, hu⟩ := h
  · left
    exact hadj.le hle
  · right
    simp only [vx_subset_of_le hle hu, and_self]

lemma Connected.le (h : G₁.Connected u v) (hle : G₁ ≤ G₂) : G₂.Connected u v := by
  induction h with
  | single huv => exact Relation.TransGen.single (huv.le hle)
  | tail huv h ih => exact Relation.TransGen.tail ih (h.le hle)

@[simp]
instance instOrderBotGraph : OrderBot (Graph α β) where
  bot := {
    V := ∅,
    E := ∅,
    Inc v e := False,
    vx_mem_of_inc := by simp only [mem_empty_iff_false, imp_self, implies_true],
    edge_mem_of_inc := by simp only [mem_empty_iff_false, imp_self, implies_true],
    exists_vertex_inc := by simp only [mem_empty_iff_false, exists_false, imp_self, implies_true],
    not_hypergraph := by simp only [IsEmpty.forall_iff, implies_true]
  }
  bot_le G := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [empty_subset]
    · simp only [empty_subset]
    · simp only [mem_empty_iff_false, false_iff, IsEmpty.forall_iff, implies_true]

instance instInhabitedGraph : Inhabited (Graph α β) where
  default := ⊥

/-- If G₁ ≤ G₂ and G₂ is finite, then G₁ is finite too. -/
theorem finite_of_le_finite {G₁ G₂ : Graph α β} (hle : G₁ ≤ G₂) [h : Finite G₂] : Finite G₁ := by
  constructor
  · -- Prove the vertex set is finite
    apply Set.Finite.subset h.vx_fin
    exact vx_subset_of_le hle
  · -- Prove the edge set is finite
    apply Set.Finite.subset h.edge_fin
    exact edge_subset_of_le hle

lemma vx_ncard_le_of_le [hfin : Finite G₂] (hle : G₁ ≤ G₂) : G₁.V.ncard ≤ G₂.V.ncard :=
  Set.ncard_le_ncard (vx_subset_of_le hle) hfin.vx_fin

lemma edge_ncard_le_of_le [hfin : Finite G₂] (hle : G₁ ≤ G₂) : G₁.E.ncard ≤ G₂.E.ncard :=
  Set.ncard_le_ncard (edge_subset_of_le hle) hfin.edge_fin

/-- Induced subgraph -/
def induce (G : Graph α β) (U : Set α) : Graph α β := by
  apply ofGraphIsBetween ⟨U, G.E ∩ {e | ∀ (x : α), G.Inc x e → x ∈ U},
    fun e x y ↦ G.IsBetween e x y ∧ x ∈ U ∧ y ∈ U, ?_, ?_, ?_, ?_, ?_⟩
  · rintro e x y ⟨hbtw, hx, hy⟩
    exact ⟨hbtw.symm, hy, hx⟩
  · rintro e x y ⟨hbtw, hx, hy⟩
    exact hx
  · rintro e x y ⟨hbtw, hx, hy⟩
    simp only [mem_inter_iff, hbtw.edge_mem, mem_setOf_eq, true_and]
    rw [forall_inc_iff hbtw]
    exact ⟨hx, hy⟩
  · rintro e he
    obtain ⟨x, y, hbtw⟩ := G.exist_IsBetween_of_mem he.1
    use x, y, hbtw
    rw [← forall_inc_iff hbtw]
    exact he.2
  · rintro e x y u v ⟨hxy, hx, hy⟩ ⟨huv, hu, hv⟩
    exact hxy.eq_or_eq_of_IsBetween huv

-- def induce (G : Graph α β) (U : Set α) : Graph α β where
--   -- change this to just V = U
--   V := G.V ∩ U
--   E := G.E ∩ {e | ∀ (x : α), G.Inc x e → x ∈ U}
--   Inc v e := G.Inc v e ∧ ∀ (x : α), G.Inc x e → x ∈ U
--   vx_mem_of_inc x y h := by
--     obtain ⟨hinc, hU⟩ := h
--     exact ⟨G.vx_mem_of_inc hinc, hU _ hinc⟩
--   edge_mem_of_inc v e h := by
--     simp only [mem_inter_iff, mem_setOf_eq]
--     obtain ⟨hinc, hU⟩ := h
--     exact ⟨hinc.edge_mem, hU⟩
--   exists_vertex_inc e he := by
--     obtain ⟨v, hv⟩ := G.exists_vertex_inc he.1
--     obtain ⟨he, hU⟩ := he
--     use v, hv, hU
--   not_hypergraph x y z e := by
--     rintro ⟨hx, _⟩ ⟨hy, _⟩ ⟨hz, hU⟩
--     obtain h | h | h := G.not_hypergraph hx hy hz <;>
--     simp only [h, true_or, or_true]

notation G "[" S "]" => Graph.induce G S

variable {U : Set α}

@[simp]
abbrev vxDel (G : Graph α β) (V : Set α) : Graph α β := G[G.V \ V]

@[simp]
lemma induce_V {U} : (G[U]).V = U := rfl

@[simp]
lemma induce_E : (G[U]).E = G.E ∩ {e | ∀ (x : α), G.Inc x e → x ∈ U} := rfl

lemma induce_E_le (U : Set α) : (G[U]).E ⊆ G.E := by
  simp [induce_E]

@[simp]
lemma induce_isBetween_iff : (G[U]).IsBetween e x y ↔ G.IsBetween e x y ∧ x ∈ U ∧ y ∈ U :=
  IsBetween.ofGraphIsBetween _

lemma IsBetween.of_IsBetween_induce (h : (G[U]).IsBetween e x y) : G.IsBetween e x y := by
  rw [induce_isBetween_iff] at h
  exact h.1

@[simp]
lemma induce_inc_iff : (G[U]).Inc v e ↔ G.Inc v e ∧ ∀ (x : α), G.Inc x e → x ∈ U := by
  simp only [induce, ofGraphIsBetween]
  constructor
  · rintro ⟨u, hbtw, hv, hu⟩
    refine ⟨hbtw.inc_left, ?_⟩
    rw [forall_inc_iff hbtw]
    exact ⟨hv, hu⟩
  · rintro ⟨hinc, hU⟩
    obtain ⟨x, y, hx⟩ := G.exist_IsBetween_of_mem hinc.edge_mem
    obtain rfl | rfl := hx.eq_of_inc hinc
    · use y, hx, hU v hx.inc_left, hU y hx.inc_right
    · use x, hx.symm, hU v hx.inc_right, hU x hx.inc_left

lemma Inc.of_Inc_induce (h : (G[U]).Inc v e) : G.Inc v e := by
  rw [induce_inc_iff] at h
  exact h.1

@[simp]
lemma induce_isLoop_iff : (G[U]).IsLoop e ↔ G.IsLoop e ∧ ∀ (x : α), G.Inc x e → x ∈ U := by
  constructor
  · rintro hloop
    simp only [IsLoop_iff_IsBetween, induce_isBetween_iff, and_self] at hloop ⊢
    obtain ⟨v, hbtw, hmem⟩ := hloop
    rw [forall_inc_iff hbtw]
    use (by use v)
  · rintro ⟨hloop, hmem⟩
    rw [IsLoop_iff_IsBetween] at hloop ⊢
    obtain ⟨v, hbtw⟩ := hloop
    rw [forall_inc_iff hbtw] at hmem
    use v
    simp [hbtw, hmem.1]

lemma IsLoop.of_Inc_induce (h : (G[U]).IsLoop e) : G.IsLoop e := by
  rw [induce_isLoop_iff] at h
  exact h.1

@[simp]
theorem induce_le_induce_iff {U V : Set α} : G[U] ≤ G[V] ↔ U ⊆ V := by
  refine ⟨vx_subset_of_le, ?_⟩
  rintro h
  refine ⟨h, ?_, ?_⟩
  · intro e
    simp +contextual only [induce_E, mem_inter_iff, mem_setOf_eq, true_and, and_imp]
    intro _he hU x hinc
    exact h (hU x hinc)
  · simp +contextual only [induce_E, mem_inter_iff, mem_setOf_eq, induce_inc_iff, implies_true,
    and_true, iff_self_and, and_imp]
    rintro v e he hU hinc
    exact fun x a ↦ h (hU x a)

@[simp]
theorem induce_eq_induce_iff {U V : Set α} : G[U] = G[V] ↔ U = V := by
  rw [le_antisymm_iff, induce_le_induce_iff, induce_le_induce_iff, antisymm_iff]

@[simp]
theorem induce_eq_self_iff {U : Set α} : G[U] = G ↔ U = G.V := by
  constructor <;> intro h
  · rw [← h]
    rfl
  · subst U
    ext1
    · simp only [induce_V]
    · ext e
      simp +contextual only [induce_E, mem_inter_iff, mem_setOf_eq, and_iff_left_iff_imp]
      exact fun a x a ↦ G.vx_mem_of_inc a
    · simp +contextual only [induce_inc_iff, and_iff_left_iff_imp]
      rintro hinc y hy
      exact hy.vx_mem

@[simp]
lemma induce_V_eq_self  : G[G.V] = G := induce_eq_self_iff.mpr rfl

@[simp]
lemma induce_empty_eq_bot : G[∅] = ⊥ := by
  ext1
  · rfl
  · ext e
    simp only [induce_E, mem_empty_iff_false, imp_false, mem_inter_iff, mem_setOf_eq,
      instOrderBotGraph, iff_false, not_and, not_forall, not_not]
    exact (G.exists_vertex_inc ·)
  · simp only [induce_V, mem_empty_iff_false, not_false_eq_true, not_inc_of_not_vx_mem,
    instOrderBotGraph]

@[simp]
lemma induce_le (G : Graph α β) {U : Set α} (hU : U ⊆ G.V) : G[U] ≤ G := by
  refine ⟨?_, ?_, ?_⟩ <;> simp +contextual [hU]

@[simp]
lemma induce_mono (G : Graph α β) (U V : Set α) (hsu : U ⊆ V) : G[U] ≤ G[V] := by
  rwa [induce_le_induce_iff]

@[simp]
lemma induce_idem (U : Set α) : G[U][U] = G[U] := by simp

/-- If a vertex is in the induced subgraph, it's in the original graph and the inducing set. -/
@[simp]
lemma mem_induce_V_iff {G : Graph α β} {v : α} {U : Set α} : v ∈ (G[U]).V ↔ v ∈ U := by simp

/-- Adjacency in induced subgraphs implies adjacency in the original graph. -/
lemma Adj.of_Adj_induce : (G[U]).Adj u v → G.Adj u v :=
  fun ⟨e, hBtw⟩ ↦ ⟨e, hBtw.of_IsBetween_induce⟩

lemma reflAdj.of_reflAdj_induce_ne : (G[U]).reflAdj u v → u ≠ v → G.reflAdj u v := by
  rintro (hAdj | ⟨rfl, hmem⟩) hne
  · exact hAdj.of_Adj_induce.reflAdj
  · exact False.elim (hne rfl)

lemma reflAdj.of_reflAdj_induce_mem : (G[U]).reflAdj u v → u ∈ G.V → G.reflAdj u v := by
  rintro (hAdj | ⟨rfl, hmem⟩) hmem
  · exact hAdj.of_Adj_induce.reflAdj
  · exact reflAdj.refl hmem

lemma reflAdj.of_reflAdj_induce_subset : (G[U]).reflAdj u v → U ⊆ G.V → G.reflAdj u v := by
  rintro (hAdj | ⟨rfl, hmem⟩) hsubset
  · exact hAdj.of_Adj_induce.reflAdj
  · exact reflAdj.refl (hsubset hmem)

theorem Connected.of_Connected_induce_mem : (G[U]).Connected u v → u ∈ G.V → G.Connected u v := by
  rintro h hmem
  induction h with
  | single hradj =>
    apply reflAdj.connected
    apply hradj.of_reflAdj_induce_mem hmem
  | tail hconn hradj ih =>
    apply Relation.TransGen.tail ih
    apply hradj.of_reflAdj_induce_mem
    exact ih.mem_right

theorem Connected.of_Connected_induce_subset : (G[U]).Connected u v → U ⊆ G.V → G.Connected u v := by
  rintro h hsubset
  induction h with
  | single hradj =>
    apply reflAdj.connected
    apply hradj.of_reflAdj_induce_subset hsubset
  | tail hconn hradj ih =>
    apply Relation.TransGen.tail ih
    exact hradj.of_reflAdj_induce_subset hsubset

lemma Inc.induce_of_mem {U : Set α} (hinc : G.Inc u e) (hU : ∀ x, G.Inc x e → x ∈ U) :
    G[U].Inc u e := by simpa [hinc]

lemma Adj.induce_of_mem {U : Set α} (hadj : G.Adj u v) (hU : ∀ x, G.reflAdj u x → x ∈ U) :
    G[U].Adj u v := by
  obtain ⟨e, hBtw⟩ := hadj
  have he : ∀ (x : α), G.Inc x e → x ∈ U := by
    rintro x hinc
    apply hU
    exact hBtw.inc_left.reflAdj_of_inc hinc
  use e
  refine ⟨?_, ?_, ?_⟩
  · simpa [hBtw.inc_left, true_and]
  · simpa [hBtw.inc_right, true_and]
  · rintro rfl
    rw [IsLoop_iff_IsBetween]
    use u
    rw [forall_inc_iff hBtw] at he
    rw [induce_isBetween_iff]
    exact ⟨hBtw, he⟩

lemma reflAdj.induce_of_mem {U : Set α} (hradj : G.reflAdj u v) (hU : ∀ x, G.reflAdj u x → x ∈ U) :
    G[U].reflAdj u v := by
  refine hradj.imp ?_ ?_
  · rintro hadj
    exact Adj.induce_of_mem hadj hU
  · rintro ⟨rfl, hu⟩
    use rfl
    exact hU u hradj

lemma Connected.induce_of_mem {U : Set α} (h : G.Connected u v) (hU : ∀ x, G.Connected u x → x ∈ U) :
    G[U].Connected u v := by
  induction h with
  | single hradj =>
    apply reflAdj.connected
    refine hradj.induce_of_mem ?_
    rintro x hradj
    exact hU _ hradj.connected
  | tail hconn hradj ih =>
    apply Relation.TransGen.tail ih
    refine hradj.induce_of_mem ?_
    rintro x hxconn
    apply hU
    exact trans hconn hxconn.connected

/-- A subgraph of a finite graph is also finite. -/
instance finite_of_finite_induce [h : Finite G] (hU : Set.Finite U) : Finite (G[U]) := by
  refine ⟨hU, ?_⟩
  apply Set.Finite.subset h.edge_fin
  simp only [induce_E, inter_subset_left]

@[simp]
lemma vx_ncard_le_of_induce [hfin : Finite G] (hU : U ⊆ G.V) : (G[U]).V.ncard ≤ G.V.ncard :=
  Set.ncard_le_ncard hU hfin.vx_fin

@[simp]
lemma edge_ncard_le_of_induce [hfin : Finite G] : (G[U]).E.ncard ≤ G.E.ncard :=
  Set.ncard_le_ncard (G.induce_E_le U) hfin.edge_fin

/-- Restrict a graph to a set of edges -/
def restrict (G : Graph α β) (R : Set β) : Graph α β where
  V := G.V
  E := G.E ∩ R
  Inc v e := G.Inc v e ∧ e ∈ R
  vx_mem_of_inc _ _ h := G.vx_mem_of_inc h.1
  edge_mem_of_inc _ _ h := ⟨h.1.edge_mem, h.2⟩
  exists_vertex_inc e he := by
    obtain ⟨v, hv⟩ := G.exists_vertex_inc he.1
    exact ⟨v, hv, he.2⟩
  not_hypergraph _ _ _ _ hex hey hez := G.not_hypergraph hex.1 hey.1 hez.1

notation G "{" S "}" => Graph.restrict G S

notation:10 G "-ᴳ" e => Graph.restrict G (Graph.E G \ {e})

@[simp]
abbrev edgeDel (G : Graph α β) (F : Set β) : Graph α β := G{G.E \ F}

variable {G : Graph α β} {R : Set β}

@[simp]
lemma restrict_V : (G{R}).V = G.V := rfl

@[simp]
lemma restrict_E : (G{R}).E = G.E ∩ R := rfl

@[simp]
lemma restrict_inc : (G{R}).Inc v e ↔ G.Inc v e ∧ e ∈ R := by
  simp only [restrict]

@[simp]
lemma restrict_le (G : Graph α β) (R : Set β) : G{R} ≤ G := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [restrict, subset_refl, inter_subset_left, mem_inter_iff,
    and_iff_left_iff_imp, and_imp]
  rintro v e he hmemR hinc
  exact hmemR

@[simp]
lemma restrict_isBetween : (G{R}).IsBetween e x y ↔ G.IsBetween e x y ∧ e ∈ R := by
  constructor
  · rintro hbtw
    refine ⟨?_, mem_of_mem_inter_right (restrict_E ▸ hbtw.edge_mem)⟩
    exact hbtw.le (restrict_le G R)
  · rintro ⟨hbtw, he⟩
    rwa [IsBetween_iff_IsBetween_of_edge_mem_le (restrict_le G R) ?_]
    simp only [restrict_E, mem_inter_iff, hbtw.edge_mem, he, and_self]

/-- If an edge is in the restricted subgraph, it's in the original graph and the restricting set. -/
@[simp]
lemma mem_restrict_E_iff {G : Graph α β} {e : β} {R : Set β} : e ∈ (G{R}).E ↔ e ∈ G.E ∧ e ∈ R := by
  simp only [restrict_E, mem_inter_iff]

/-- Adjacency in restricted subgraphs implies adjacency in the original graph. -/
lemma Adj.of_Adj_restrict {G : Graph α β} {u v : α} {R : Set β} :
    (G{R}).Adj u v → G.Adj u v := (Adj.le · (restrict_le G R))

/-- Connectedness in a restricted subgraph implies connectedness in the original graph. -/
theorem Connected.of_Connected_restrict {G : Graph α β} {u v : α} {R : Set β} :
    (G{R}).Connected u v → G.Connected u v :=
  (Connected.le · (restrict_le G R))

lemma restrict_le_restrict_of_le (hle : G₁ ≤ G₂) {S R : Set β} (hSR : S ⊆ R) : G₁{S} ≤ G₂{R} := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [restrict, vx_subset_of_le hle, subset_inter_iff, mem_inter_iff,
  and_imp]
  · refine ⟨?_, ?_⟩
    · rintro x ⟨H1, H2⟩
      exact edge_subset_of_le hle H1
    · rintro x ⟨H1, H2⟩
      exact hSR H2
  · rintro v e he1 heS
    rw [Inc_iff_Inc_of_edge_mem_le hle he1]
    simp only [heS, and_true, hSR heS]

lemma reflAdj.restrict_of_le_reflAdj_restrict (hle : G₁ ≤ G₂) {S : Set β}
    (hSradj : G₂{S}.reflAdj u v) (h : G₂.E ∩ S ⊆ G₁.E) (hu : u ∈ G₁.V) : G₁{S}.reflAdj u v := by
  have := restrict_le_restrict_of_le hle (Subset.rfl : S ⊆ S)
  refine hSradj.imp ?_ ?_
  · rintro ⟨e, hBtw⟩
    use e
    rwa [IsBetween_iff_IsBetween_of_edge_mem_le this ?_]
    · have he2S := hBtw.edge_mem
      exact ⟨h he2S, he2S.2⟩
  · simp only [restrict_V, and_imp]
    rintro rfl hu2
    use rfl

lemma Connected.restrict_of_le_inter_subset (hle : G₁ ≤ G₂) {S : Set β}
    (hSconn : G₂{S}.Connected u v) (h : G₂.E ∩ S ⊆ G₁.E) (hu : u ∈ G₁.V) : G₁{S}.Connected u v := by
  induction hSconn with
  | single hradj =>
    rename_i v
    apply reflAdj.connected
    apply hradj.restrict_of_le_reflAdj_restrict hle h hu
  | tail _hconn hradj ih =>
    apply ih.trans
    rename_i x y
    apply reflAdj.connected
    apply hradj.restrict_of_le_reflAdj_restrict hle h
    exact ih.symm.mem_left

lemma restrict_Connected_iff_restrict_Connected_of_le (hle : G₁ ≤ G₂) {S : Set β}
    (h : G₂.E ∩ S ⊆ G₁.E) (hu : u ∈ G₁.V) :
    G₁{S}.Connected u v ↔ G₂{S}.Connected u v := by
  constructor <;> rintro hconn
  · refine Connected.le hconn ?_
    exact restrict_le_restrict_of_le hle fun ⦃a⦄ a ↦ a
  · exact Connected.restrict_of_le_inter_subset hle hconn h hu

@[simp]
theorem restrict_le_restrict_iff (G : Graph α β) (R S : Set β) :
    G{R} ≤ G{S} ↔ G.E ∩ R ⊆ G.E ∩ S := by
  refine ⟨edge_subset_of_le, ?_⟩
  rintro h
  refine ⟨subset_rfl, h, ?_⟩
  simp only [restrict_inc, and_congr_right_iff]
  rintro v e he hinc
  simp [he.2, (h he).2]

@[simp]
theorem restrict_eq_restrict_iff (G : Graph α β) (R S : Set β) :
    G{R} = G{S} ↔ G.E ∩ R = G.E ∩ S := by
  rw [le_antisymm_iff, subset_antisymm_iff, restrict_le_restrict_iff, restrict_le_restrict_iff]

@[simp]
theorem restrict_eq_self_iff (G : Graph α β) (R : Set β) : G{R} = G ↔ G.E ⊆ R := by
  constructor <;> intro h
  · rw [← h]
    simp only [restrict_E, inter_subset_right]
  · ext1
    · simp only [restrict]
    · simp only [restrict_E, inter_eq_left, h]
    · simp only [restrict_inc, and_iff_left_iff_imp]
      intro hinc
      exact h hinc.edge_mem

@[simp]
lemma restrict_univ_eq_self : G{Set.univ} = G := by
  rw [restrict_eq_self_iff]
  exact subset_univ _

@[simp]
lemma restrict_E_eq_self : G{G.E} = G := by
  rw [restrict_eq_self_iff]

lemma restrict_E_subset_singleton (e : β) : G{{e}}.E ⊆ {e} := by simp

@[simp]
lemma restrict_mono (G : Graph α β) (R S : Set β) (h : R ⊆ S) : G{R} ≤ G{S} := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [restrict, subset_refl, inter_subset_left, mem_inter_iff,
    and_iff_left_iff_imp, and_imp]
  · exact inter_subset_inter (fun ⦃a⦄ a ↦ a) h
  · rintro v e he hmemR
    simp only [hmemR, and_true, h hmemR]

@[simp]
theorem restrict_restrict_eq_restrict_inter (R S : Set β) : G{R}{S} = G{R ∩ S} := by
  ext1
  · simp only [restrict, inter_assoc, mem_inter_iff]
  · simp only [restrict, mem_inter_iff]
    rw [← inter_assoc]
  · rename_i v e
    simp only [restrict, mem_inter_iff]
    rw [and_assoc]

@[simp]
lemma restrict_idem (R : Set β) : G{R}{R} = G{R} := by
  convert G.restrict_restrict_eq_restrict_inter R R
  simp only [inter_self]

/-- A restricted subgraph of a finite graph is also finite. -/
instance finite_of_finite_restrict {R : Set β} [h : Finite G] : Finite (G{R}) := by
  constructor
  · -- Prove the vertex set is finite
    simp only [restrict_V]
    exact h.vx_fin
  · -- Prove the edge set is finite
    apply Set.Finite.subset h.edge_fin
    simp only [restrict_E, inter_subset_left]

@[simp]
lemma vx_ncard_le_of_restrict [hfin : Finite G] : (G{R}).V.ncard ≤ G.V.ncard :=
  Set.ncard_le_ncard (vx_subset_of_le (restrict_le G R)) hfin.vx_fin

@[simp]
lemma edge_ncard_le_of_restrict [hfin : Finite G] : (G{R}).E.ncard ≤ G.E.ncard :=
  Set.ncard_le_ncard (edge_subset_of_le (restrict_le G R)) hfin.edge_fin

@[simp]
lemma EdgeDel_singleton_isBetween_iff_isBetween_of_ne {e' : β} (hne : e ≠ e') :
    (G -ᴳ e).IsBetween e' u v ↔ G.IsBetween e' u v := by
  refine ⟨fun h ↦ h.le (restrict_le G _), fun h ↦ by
    simp [restrict_isBetween, h, hne.symm, h.edge_mem]⟩

lemma IsLoop.reflAdj_iff_edgeDel_singleton (he : G.IsLoop e) :
    (G -ᴳ e).reflAdj u v ↔ G.reflAdj u v := by
  constructor <;> rintro h
  · exact h.le (restrict_le G _)
  · obtain ⟨e', hbtw⟩ | ⟨rfl, hu⟩ := h
    · by_cases h' : e = e'
      · subst e'
        rw [hbtw.IsLoop_iff_eq] at he
        subst v
        exact reflAdj.refl hbtw.vx_mem_left
      · apply Adj.reflAdj
        use e'
        rwa [EdgeDel_singleton_isBetween_iff_isBetween_of_ne h']
    · exact reflAdj.of_vxMem hu

lemma IsLoop.connected_iff_edgeDel_singleton (he : G.IsLoop e) :
    (G -ᴳ e).Connected u v ↔ G.Connected u v:= by
  constructor <;> rintro h
  · exact h.le (restrict_le G _)
  · induction h with
    | single hradj =>
      apply reflAdj.connected
      rwa [reflAdj_iff_edgeDel_singleton he]
    | tail hconn hradj ih =>
      apply ih.tail
      rwa [reflAdj_iff_edgeDel_singleton he]

lemma induce_induce_eq_induce_restrict' (U V : Set α) : G[U][V] = G{G[U].E}[V] := by
  ext1
  · simp only [induce_V, induce_E, restrict_V]
  · ext e
    simp +contextual only [induce_E, induce_inc_iff, and_imp, mem_inter_iff, mem_setOf_eq,
      restrict_E, restrict_inc, and_self_left, iff_def, implies_true, and_self, imp_self]
  · rename_i v e
    simp +contextual only [induce_inc_iff, and_imp, induce_E, restrict_inc, mem_inter_iff,
      mem_setOf_eq, iff_def, implies_true, and_self, and_true, true_and, forall_const, imp_self]
    exact fun a a_1 a_2 ↦ a.edge_mem

@[simp]
lemma induce_induce_eq_induce_restrict (U V : Set α) : G[U][V] = G{{e | ∀ (x : α), G.Inc x e → x ∈ U}}[V] := by
  rw [induce_induce_eq_induce_restrict' U V, induce_E]
  congr 1
  rw [restrict_eq_restrict_iff]
  simp

/-- G{R}[U] is the prefered notation for explicit subgraph over G[U]{R} -/
lemma induce_restrict_eq_restrict_induce (U : Set α) (R : Set β) :
    G[U]{R} = G{R}[U] := by
  ext1
  · simp only [restrict_V, induce_V]
  · ext e
    simp +contextual only [restrict_E, induce_E, mem_inter_iff, mem_setOf_eq, restrict_inc, and_imp,
      iff_def, and_self, imp_self, implies_true]
  · rename_i v e
    simp +contextual only [restrict_inc, induce_inc_iff, and_imp, iff_def, and_self, imp_self,
      implies_true]

/-- From here `subgraph` refers to G{R}[U] -/
@[simp]
theorem induce_restrict_eq_subgraph (U : Set α) (R : Set β) :
    G[U]{R} = G{R}[U] := G.induce_restrict_eq_restrict_induce U R

lemma subgraph_eq_induce (h : {e | ∀ (x : α), G.Inc x e → x ∈ U} ⊆ R) : G{R}[U] = G[U] := by
  ext1
  · rfl
  . simp only [induce_E, restrict_E, restrict_inc, and_imp]
    rw [inter_assoc]
    congr 1
    ext e
    simp +contextual only [mem_inter_iff, mem_setOf_eq, iff_def, implies_true, and_true, true_and]
    apply h
  · simp +contextual only [induce_inc_iff, restrict_inc, and_imp, iff_def, implies_true, and_self,
    true_and, and_true]
    rintro hinc
    apply h

lemma subgraph_le (G : Graph α β) (R : Set β) {U : Set α} (hU : U ⊆ G.V) : G{R}[U] ≤ G :=
  (Graph.induce_le _ (by exact hU : U ⊆ G{R}.V)).trans (G.restrict_le R)

/-- Implicit subgraph iff explicit subgraph-/
theorem exists_subgraph_of_le (hle : G₁ ≤ G₂) : G₁ = G₂{G₁.E}[G₁.V] := by
  ext1
  · simp only [induce_V]
  · ext e
    simp +contextual only [induce_E, restrict_E, restrict_inc, and_imp, mem_inter_iff,
      mem_setOf_eq, iff_def, and_true, forall_const, implies_true]
    rintro he
    use edge_subset_of_le hle he
    obtain ⟨x, y, hBtw⟩ := exist_IsBetween_of_mem (edge_subset_of_le hle he)
    rw [forall_inc_iff hBtw]
    rw [← IsBetween_iff_IsBetween_of_edge_mem_le hle he] at hBtw
    exact ⟨hBtw.vx_mem_left, hBtw.vx_mem_right⟩
  · simp +contextual only [induce_inc_iff, restrict_inc, and_imp, iff_def, forall_const]
    constructor
    · rintro hinc1
      use ⟨hinc1.le hle, hinc1.edge_mem⟩
      rintro x hinc2 hmem1
      rw [← Inc_iff_Inc_of_edge_mem_le hle hmem1] at hinc2
      exact hinc2.vx_mem
    · rintro h2inc h1e hforall
      exact (Inc_iff_Inc_of_edge_mem_le hle h1e).mpr h2inc


@[mk_iff]
structure IsVxSeparator (G : Graph α β) (u v : α) (S : Set α) : Prop where
  not_mem_left : u ∉ S
  not_mem_right : v ∉ S
  not_connected : ¬ (G [G.V \ S]).Connected u v

lemma not_exists_isSeparator_self (hu : u ∈ G.V) : ¬ ∃ S, G.IsVxSeparator u u S :=
  fun ⟨S, hS⟩ ↦ hS.not_connected <| Connected.refl <| by simp [hu, hS.not_mem_left]

lemma IsVxSeparator.iff_edgeDel_singleton_isLoop {S : Set α} (he : G.IsLoop e) :
    G.IsVxSeparator u v S ↔ (G -ᴳ e).IsVxSeparator u v S := by
  refine ⟨fun ⟨hu, hv, hconn⟩ ↦ ⟨hu, hv, ?_⟩, fun ⟨hu, hv, hconn⟩ ↦ ⟨hu, hv, ?_⟩⟩
  · by_cases he' : e ∈ G[G.V \ S].E
    · rw [restrict_V, ← induce_restrict_eq_subgraph]
      rw [← IsLoop.connected_iff_edgeDel_singleton (e := e)] at hconn
      convert hconn using 2
      rw [restrict_eq_restrict_iff]
      ext e
      simp +contextual only [induce_E, mem_diff, mem_inter_iff, mem_setOf_eq, mem_singleton_iff,
        and_self_left, and_congr_right_iff, true_and, implies_true]
      rwa [IsLoop_iff_IsLoop_of_edge_mem_le (induce_le G diff_subset) he']
    · rwa [restrict_V, subgraph_eq_induce]
      rintro e'
      simp +contextual only [mem_diff, mem_setOf_eq, mem_singleton_iff]
      rintro hx
      sorry
  · sorry

def IsVxConnected (G : Graph α β) (n : ℕ) : Prop :=
  ∀ S : Finset α, S.card < n → (G[G.V \ S]).Conn

lemma IsVxConnected.one_of_conn [G.Conn] : G.IsVxConnected 1 := by
  simpa [IsVxConnected]

def IsEdgeConnected (G : Graph α β) (n : ℕ) : Prop :=
  ∀ U : Finset β, U.card < n → (G{Uᶜ}).Conn

lemma IsEdgeConnected.one_of_conn [G.Conn] : G.IsEdgeConnected 1 := by
  rintro S hS
  simp only [Nat.lt_one_iff, Finset.card_eq_zero] at hS
  subst S
  simp only [Finset.coe_empty, compl_empty, restrict_univ_eq_self]
  assumption
