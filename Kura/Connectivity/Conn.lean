import Kura.Connectivity.Walk
import Kura.Graph.Remove
import Kura.Dep.Rel
import Kura.Graph.Searchable
import Kura.Dep.Equiv
import Kura.Dep.Quot


namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] {G : Graph V E}


def conn (G : Graph V E) : V → V → Prop := Relation.ReflTransClosure G.adj

@[simp]
lemma conn.refl (G : Graph V E) (v : V) : G.conn v v := Relation.ReflTransGen.refl

lemma conn.symm {G : Graph V E} [Undirected G] (u v : V) : G.conn u v → G.conn v u := by
  apply Relation.ReflTransGen.symmetric
  rintro u v h
  rwa [G.adj_comm]

lemma conn_comm {G : Graph V E} [Undirected G] (u v : V) : G.conn u v ↔ G.conn v u :=
  ⟨ conn.symm u v, conn.symm v u ⟩

lemma conn.trans {G : Graph V E} {u v w : V} : G.conn u v → G.conn v w → G.conn u w :=
  Relation.ReflTransGen.trans

lemma conn.ofAdj {G : Graph V E} {u v : V} (h : G.adj u v) : G.conn u v :=
    Relation.ReflTransGen.single h

lemma SubgraphOf.conn {G : Graph V E} {H : Graph W F} (h : G ⊆ᴳ H) {u v : V} (huv : G.conn u v) :
    H.conn (h.fᵥ u) (h.fᵥ v) := by
  induction huv with
  | refl => exact conn.refl _ _
  | tail _h1 h2 IH => exact IH.tail (h.adj h2)

lemma PathGraph_conn_0 (n : ℕ) (v : Fin (n+1)) : (PathGraph n).conn 0 v := by
  induction' v with j hjpos
  induction' j with x ih
  · exact conn.refl (PathGraph n) 0
  · specialize ih (by omega)
    apply ih.tail ; clear ih
    rw [PathGraph.adj_iff]
    simp only [Fin.mk_lt_mk, lt_add_iff_pos_right, zero_lt_one]

lemma conn.path (u v : V) (huv : G.conn u v) : ∃ P : G.Path, P.start = u ∧ P.finish = v := by
  unfold conn at huv
  induction huv with
  | refl => exact ⟨Path.nil u, rfl, rfl⟩
  | tail _h hadj IH =>
    rename_i x y
    obtain ⟨P, hPstart, hPfinish⟩ := IH
    obtain ⟨e, he⟩ := hadj
    by_cases h : x = y
    · subst h
      refine ⟨P, hPstart, hPfinish⟩
    · use P.append (Path.some x e y he h) (by rw [hPfinish, Path.some_start])
      refine ⟨ ?_, ?_ ⟩
      · rwa [Path.append_start]
      · rw [Path.append_finish, Path.some_finish]

lemma conn.ofPath (P : G.Path) : G.conn P.start P.finish := by
  apply List.relationReflTransGen_of_exists_chain P.vertices.tail
  · suffices List.Chain' G.adj (P.start :: P.vertices.tail) by
      exact this
    rw [← Walk.vertices_head_eq_start, List.head_cons_tail]
    exact Walk.vertices_chain'_adj P.toWalk
  · simp only [← Walk.vertices_head_eq_start, List.head_cons_tail, Walk.vertices_getLast_eq_finish]

lemma conn.OfPathSubgraphOf {u v : V} {n : ℕ} (S : (PathGraph n) ⊆ᴳ G) (hSstart : S.fᵥ 0 = u)
    (hSfinish : S.fᵥ n = v) : G.conn u v := by
  have h := PathGraph_conn_0 n n
  rw [← hSstart, ← hSfinish]
  exact S.conn h

lemma conn.PathSubgraphOf {u v : V} (huv : G.conn u v) : ∃ (n : ℕ) (S : (PathGraph n) ⊆ᴳ G),
    S.fᵥ 0 = u ∧ S.fᵥ n = v := by
  obtain ⟨P, hPstart, hPfinish⟩ := huv.path
  refine ⟨P.length, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · exact fun v => P.vertices.get (v.cast P.vertices_length.symm)
  · exact fun e => P.edges.get (e.cast P.edges_length.symm)
  · intro e
    simp

  sorry


  -- change Relation.ReflTransGen G.adj u v at huv
  -- obtain ⟨l, hChain, hv, hnodup⟩ := List.exists_nodup_chain_of_relationReflTransGen huv
  -- rw [List.chain_iff_forall₂] at hChain
  -- obtain rfl | hForall := hChain
  -- · simp only [List.getLast_singleton] at hv
  --   subst u
  --   refine ⟨0, ⟨⟨fun a ↦ v, Fin.elim0, (Fin.elim0 ·)⟩, ?_, ?_⟩, ?_, ?_⟩ <;>
  --     simp only [Nat.reduceAdd] <;> rintro a b _hab
  --   · exact Subsingleton.elim a b
  --   · exact a.elim0
  -- · use l.length
  --   obtain ⟨hlen, hadj⟩ := List.forall₂_iff_zip.mp hForall
  --   have hadjp : ∀ p ∈ (u :: l.dropLast).zip l, G.adj p.1 p.2 := by
  --     rintro ⟨a, b⟩ h
  --     exact hadj h
  --   clear hadj hForall
  --   let le : List E := (u :: l.dropLast).zip l |>.pmap (fun _p h ↦ h.choose) hadjp

  --   refine ⟨⟨⟨(u :: l).get, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  --   · rintro i
  --     apply (le.get <| i.cast ·)
  --     rw [List.length_pmap, List.length_zip, hlen, min_self]
  --   · rintro i
  --     unfold PathGraph
  --     simp only [canGo, List.get_eq_getElem, Fin.coe_cast, List.getElem_pmap, List.getElem_zip,
  --       Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, map_undir, List.length_cons, Sym2.map_pair_eq,
  --       Fin.coe_castSucc, Fin.val_succ, List.getElem_cons_succ, le]


  --     sorry
  --   · rintro i j hij
  --     simp only [List.get_eq_getElem, List.length_cons] at hij
  --     rw [hnodup.getElem_inj_iff] at hij
  --     omega
  --   save
  --   · suffices le.Nodup by
  --       rintro i j hij
  --       simp only [List.get_eq_getElem, Fin.coe_cast] at hij
  --       rw [this.getElem_inj_iff] at hij
  --       omega
  --     rw [List.nodup_iff_injective_getElem]
  --     by_contra! h
  --     sorry
  --   · simp only [List.get_eq_getElem, List.length_cons, Fin.val_zero, List.getElem_cons_zero]
  --   · simp only [Fin.natCast_eq_last, List.get_eq_getElem, List.length_cons, Fin.val_last]
  --     rw [List.getLast_eq_getElem] at hv
  --     exact hv


instance instConnDec [Fintype V] [G.SearchableOut]: DecidableRel G.conn :=
  Relation.ReflTransGenDeciable

example : (CycleGraph 12 (by omega)).conn 0 6 := by decide

class connected (G : Graph V E) : Prop where
  all_conn : ∀ u v : V, conn G u v

def all_conn (u v : V) [G.connected] : conn G u v := connected.all_conn u v

@[simp]
lemma not_connected : ¬ G.connected ↔ ∃ u v, ¬ G.conn u v := by
  refine ⟨ ?_, ?_ ⟩
  · intro h
    by_contra! h'
    exact h (connected.mk h')
  · rintro ⟨u, v, h⟩ h'
    exact h (h'.all_conn u v)

lemma instSpanningSubgraphOfConnected {G : Graph V E} {H : Graph W F} [G.connected]
  (h : G.SpanningSubgraphOf H) : H.connected where
  all_conn u v := by
    have : G.conn (h.fᵥEquiv.symm u) (h.fᵥEquiv.symm v) := G.all_conn _ _
    convert h.conn this <;>
    · change _ = h.fᵥEquiv (h.fᵥEquiv.symm _)
      exact (Equiv.symm_apply_eq h.fᵥEquiv).mp rfl

instance instPathGraphConn (n : ℕ) : (PathGraph n).connected where
  all_conn u v := ((PathGraph_conn_0 n u).symm (G:=PathGraph n) _).trans (PathGraph_conn_0 n v)

def connSetoid (G : Graph V E) [Undirected G] : Setoid V where
  r := conn G
  iseqv := by
    refine ⟨ ?_, ?_, ?_ ⟩
    · intro a
      exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.symmetric
      intro x y hxy
      exact (G.adj_comm x y).mp hxy
    · exact Relation.ReflTransGen.trans

lemma connSetoid_eq_bot_of_IsEmpty_E [IsEmpty E] (G : Graph V E) [Undirected G] :
    connSetoid G = ⊥ := by
  apply Setoid.ext
  rintro a b
  change Relation.ReflTransGen G.adj a b ↔ _
  simp only [adj_eq_bot_of_IsEmpty_E, Setoid.bot_def]
  rw [Relation.reflTransGen_iff_eq, Eq.comm]
  simp only [Pi.bot_apply, «Prop».bot_eq_false, not_false_eq_true, implies_true]

lemma connSetoid_eq_top_of_connected [Undirected G] [G.connected] : connSetoid G = ⊤ := by
  apply Setoid.ext
  rintro a b
  change G.conn a b ↔ _
  simp only [Setoid.top_def, Pi.top_apply, «Prop».top_eq_true, iff_true]
  exact G.all_conn a b

lemma connSetoid_Es_le_connSetoid [Undirected G] (S : Set E) :
    (G{S}ᴳ).connSetoid ≤ G.connSetoid := by
  rintro a b
  simp only [connSetoid, conn]
  apply Relation.ReflTransClosure.monotone
  convert G.Es_spanningsubgraph S |>.toHom.adj_le
  simp only [Es_spanningsubgraph_fᵥ, Relation.map_id_id]

def NumberOfComponents [Fintype V] [Fintype E] (G : Graph V E) [Undirected G] : ℕ :=
  @Fintype.card (Quotient (connSetoid G)) (@Quotient.fintype V _ (connSetoid G) Relation.ReflTransGenDeciable)

lemma NumberOfComponents_le_card_V [Fintype V] [Fintype E] [Undirected G] :
    G.NumberOfComponents ≤ Fintype.card V := by
  unfold NumberOfComponents
  exact @Fintype.card_quotient_le V _ G.connSetoid Relation.ReflTransGenDeciable

lemma NumberOfComponents_eq_card_V [Fintype V] [IsEmpty E] [Fintype E] (G : Graph V E)
    [Undirected G] : G.NumberOfComponents = Fintype.card V := by
  unfold NumberOfComponents
  rw [@Fintype.card_eq]
  refine ⟨Equiv.symm ?_⟩
  convert Equiv.Quotient_bot
  apply connSetoid_eq_bot_of_IsEmpty_E

lemma NumberOfComponents_le_one [Fintype V] [Fintype E] (G : Graph V E) [Undirected G] [G.connected] :
    G.NumberOfComponents ≤ 1 := by
  unfold NumberOfComponents
  rw [@Fintype.card_le_one_iff_subsingleton, connSetoid_eq_top_of_connected]
  exact SubsingletonQuotientTop

lemma NumberOfComponents_eq_one [Fintype V] [Fintype E] [Nonempty V] (G : Graph V E) [Undirected G]
    [G.connected] : G.NumberOfComponents = 1 := by
  refine le_antisymm (G.NumberOfComponents_le_one) ?_
  unfold NumberOfComponents
  rw [Nat.one_le_iff_ne_zero, ne_eq, @Fintype.card_eq_zero_iff, Quotient.IsEmpty_iff]
  exact not_isEmpty_of_nonempty V


lemma VSubsingletonofConnectedEcardZero [Fintype E] [G.connected] (hE : Fintype.card E = 0):
  Subsingleton V := by
  apply Subsingleton.intro
  rintro a b
  obtain ⟨w, rfl, rfl⟩ := (G.all_conn a b).path
  by_cases h : w.length = 0
  · rw [w.length_eq_zero_iff] at h
    exact (w.finish_eq_start h).symm
  · exfalso
    rw [← ne_eq, Nat.ne_zero_iff_zero_lt, Walk.length, List.length_pos_iff_exists_mem] at h
    obtain ⟨⟨ u, e, v ⟩, he⟩ := h
    rw [Fintype.card_eq_zero_iff] at hE
    exact hE.false e

lemma Es_subgraph_conn_eq_conn_iff {G : Graph V E} [Undirected G] {S : Set E}
  (hS : ∀ e ∉ S, G{S}ᴳ.conn (G.v1 e) (G.v2 e)) (u v : V) :
    G{S}ᴳ.conn u v ↔ G.conn u v := by
  let G' := G{S}ᴳ
  let hSubgraph : G' ⊆ᴳ G := (Es_spanningsubgraph G S).toSubgraphOf
  have := hSubgraph.Undirected
  have hadj : G'.adj ≤ G.adj := fun _ _ => hSubgraph.adj
  have hconn : G'.conn ≤ G.conn := Relation.ReflTransClosure.monotone hadj

  have hadj' : G.adj ≤ G'.conn := by
    rintro a b ⟨e', he'⟩
    by_cases h : e' ∈ S
    · have : G'.adj a b := ⟨⟨e', by simp only [Set.mem_compl_iff, h, not_false_eq_true]⟩, he'⟩
      exact Relation.ReflTransGen.single this
    · simp only [canGo, inc_eq_undir_v12, canGo_iff_eq_of_undir, Sym2.eq, Sym2.rel_iff',
        Prod.mk.injEq, Prod.swap_prod_mk] at he'
      rcases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      on_goal 2 => rw [conn_comm]
      all_goals exact hS e' h

  have hconn' : G.conn ≤ G'.conn := by
    convert Relation.ReflTransClosure.monotone hadj'
    exact (Relation.ReflTransClosure.idempotent _).symm

  rw [le_antisymm hconn hconn']

-- lemma Es_singleton_compliment_NumberOfComponents_eq_NumberOfComponents_or_NumberOfComponents_pred
--   [Fintype V] [Fintype E] [Searchable G] [Undirected G] (e : E) :
--     G{{e}ᶜ}ᴳ.NumberOfComponents = G.NumberOfComponents ∨ G{e}ᴳ.NumberOfComponents = G.NumberOfComponents - 1 := by
--   sorry

lemma exist_edge [Nonempty E] (G : Graph V E) [fullGraph G] [G.connected] (v : V) :
    ∃ e, v ∈ G.inc e := by
  sorry

noncomputable def FintypeVofFintypeEconnected [Fintype E] [fullGraph G] [G.connected] : Fintype V := by
  by_cases h : IsEmpty E
  · refine @Fintype.ofSubsingleton V sorry (G.VSubsingletonofConnectedEcardZero ?_)
    exact Fintype.card_eq_zero
  · simp at h
    use Finset.univ.biUnion (G.endAt · |>.toFinset)
    rintro x
    simp only [endAt, Finset.mem_biUnion, Finset.mem_univ, Multiset.mem_toFinset, true_and]
    exact G.exist_edge x

lemma n_pred_le_m_of_connected [Fintype V] [Fintype E] [G.connected] :
    Fintype.card V - 1 ≤ Fintype.card E := by
  sorry

def componentOf (v : V) : Set V := {u | G.conn u v}

/--
cut is a vertex cut
edgeCut is an edge cut
-/
def isCutBetween (u v : V) (S : Set V) : Prop :=
    ∃ (hu : u ∉ S) (hv : v ∉ S), G.conn u v ∧ ¬ (G[Sᶜ]ᴳ).conn ⟨u, hu⟩ ⟨v, hv⟩

def isCut (S : Set V) : Prop := ∃ (u v : V), G.isCutBetween u v S

def isMinimalCut (S : Set V) : Prop := Minimal (G.isCut ·) S

lemma cut_of_minCut (S : Set V) (h : G.isMinimalCut S) : G.isCut S := by
  unfold isMinimalCut Minimal at h
  exact h.1

lemma empty_not_cut : ¬ G.isCut ∅ := by
  rintro ⟨ u', v', _hu', _hv', ⟨hConn, hnConn⟩⟩
  apply hnConn
  convert G.Vs_empty_compl.symm.conn hConn <;> simp only [all, Vs_empty_compl, Isom.symm_fᵥ,
    Isom.trans_fᵥEquiv, Vs_congr_fᵥEquiv, Vs_univ_fᵥEquiv, Equiv.symm_trans_apply,
    Equiv.setCongr_symm, Equiv.Set.univ_symm_apply, Equiv.setCongr_apply]

structure connectivityBetween (u v : V) (k : ℕ) where
  P : Finset G.Path
  hPcard : P.card = k
  hPstart : ∀ p ∈ P, p.start = u
  hPfinish : ∀ p ∈ P, p.finish = v
  hPdisjoint : ⋂ p ∈ P, p.vertices.toFinset = {u, v}

def connectivity (G : Graph V E) (k : ℕ) : Prop := ∀ u v, Nonempty <| G.connectivityBetween u v k

lemma connectivityBetween_le_cutBetween (u v : V) {X : Finset V} (hX : G.isCutBetween u v X) :
    IsEmpty <| G.connectivityBetween u v (X.card + 1) := by
  by_contra! h
  simp only [not_isEmpty_iff] at h
  obtain ⟨P, hPcard, hPstart, hPfinish, hPdisjoint⟩ := h
  obtain ⟨hu, hv, hconn, hnConn⟩ := hX
  have hPexist : ∃ p ∈ P, Disjoint p.vertices.toFinset X := by
    by_contra! h
    simp_rw [Finset.not_disjoint_iff_nonempty_inter] at h
    unfold Finset.Nonempty at h
    sorry
  obtain ⟨p, hp, hDisjoint⟩ := hPexist
  sorry

-- lemma Menger (n : ℕ) : (∃ (S : Finset V), S.card = n ∧ G.minCut S) ↔
--     ∃ (SP : Finset G.Path), SP.card = n ∧

def edgeCut' (S : Set E) : Prop :=
  ∃ u v, G.conn u v ∧ ∀ w : Walk G, w.start = u ∧ w.finish = v → ∃ e ∈ S, e ∈ w.edges

@[simp]
def edgeCut (S : Set E) : Prop := ∃ u v, G.conn u v ∧ ¬ G{Sᶜ}ᴳ.conn u v

lemma edgeCut_of_not_conn (S : Set E) (u v : V) (hG : G.conn u v)
  (hGS : ¬ G{Sᶜ}ᴳ.conn u v) : G.edgeCut S := ⟨ u, v, hG, hGS ⟩

lemma empty_not_edgeCut (G : Graph V E) : ¬ G.edgeCut ∅ := by
  rintro ⟨ u', v', hG', hGS ⟩
  apply hGS
  have : (∅ : Set E)ᶜ = Set.univ := by
    simp only [Set.compl_empty]
  convert (G.Es_congr this |>.trans G.Es_univ).symm.conn hG' <;>
  simp only [Isom.symm_fᵥ, Isom.trans_fᵥEquiv, Es_congr_fᵥEquiv, Es_univ_fᵥEquiv,
    Equiv.trans_refl, Equiv.refl_symm, Equiv.refl_apply]

lemma edgeCut_upward_closed {S T : Set E} (hST : S ⊆ T) (hCut : G.edgeCut S) : G.edgeCut T := by
  unfold edgeCut at hCut ⊢
  contrapose! hCut
  intro u v hG
  obtain ⟨P, hPstart, hPfinish⟩ := (hCut u v hG).path
  obtain ⟨P', hP'start, hP'finish⟩ : ∃ P' : (G.Es Sᶜ).Path, P'.start = u ∧ P'.finish = v := by
    have hSTset : (T : Set E)ᶜ ⊆ (↑S)ᶜ := Set.compl_subset_compl_of_subset hST
    use (G.Es_spanningsubgraph_Es_of_subset hSTset).Path P
    simp only [Es_spanningsubgraph_Es_of_subset, SubgraphOf.Path_start, hPstart, id_eq,
      SubgraphOf.Path_finish, hPfinish, and_self]
  rw [← hP'start, ← hP'finish]
  exact conn.ofPath P'

def bridge (e : E) : Prop := G.connected ∧ G.edgeCut {e}

def minEdgeCut (S : Set E) : Prop :=
  Minimal (G.edgeCut ·) S

lemma edgeCut_of_minEdgeCut (S : Set E) (h : G.minEdgeCut S) : G.edgeCut S := by
  unfold minEdgeCut Minimal at h
  exact h.1

lemma empty_not_minEdgeCut : ¬ G.minEdgeCut ∅ := by
  rintro ⟨ hCut, _hMin ⟩
  exact empty_not_edgeCut _ hCut

-- def isolatingEdgeCut [Searchable G] (v : V) := G.incEdges v

lemma incEdges_edgeCut (v : V) [Nontrivial V] [Searchable G] [DecidableEq E] :
    G.edgeCut (G.incEdges v).toFinset := by
  simp only [edgeCut]
  obtain ⟨w, hw⟩ := exists_ne v
  sorry

lemma bridge_minEdgeCut (e: E) (h: G.bridge e) : G.minEdgeCut {e} := by
  unfold minEdgeCut Minimal
  obtain ⟨ _, hCut⟩ := h
  refine ⟨ hCut, ?_ ⟩
  rintro S hS Sle
  have : S.Nonempty := by
    by_contra! h
    subst h
    exact empty_not_edgeCut _ hS
  simp_all only [edgeCut, Set.le_eq_subset, Set.subset_singleton_iff, Set.singleton_subset_iff]
  obtain ⟨a, ha⟩ := this
  convert ha
  exact (Sle a ha).symm

class NEdgeConnected (n : ℕ) extends connected G where
  no_small_cut : ∀ S : Finset E, S.card < n → ¬ G.edgeCut S

def ball (u : V) (n : ℕ) : Set V :=
  {v | ∃ w : Walk G, w.start = u ∧ w.length ≤ n ∧ w.finish = v}

class NConnected [fullGraph G] (n : ℕ) : Prop where
  all_conn : ∀ u v : V, conn G u v
  h : ∀ S : Finset V, S.card ≤ n → G[Sᶜ]ᴳ.connected
