import Kura.Connectivity.closedWalk
import Kura.Connectivity.Conn
import Kura.Examples.Conn
import Kura.Graph.Remove

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W]


def acyclic (G : Graph V E) : Prop := ∀ n, IsEmpty <| CycleGraph n ⊆ᴳ G

omit [DecidableEq V] in @[simp]
lemma not_acyclic_iff_cycle {G : Graph V E} :
    ¬ G.acyclic ↔ ∃ n, ∃ (_ : CycleGraph n ⊆ᴳ G), True := by
  simp only [acyclic, not_forall, not_isEmpty_iff]
  rw [exists_congr]
  intro n
  constructor
  · rintro ⟨S⟩
    use S
  · rintro ⟨S⟩
    exact ⟨S⟩

omit [DecidableEq V] in
lemma acyclic_of_IsEmpty_E {G : Graph V E} [IsEmpty E] : G.acyclic := by
  simp only [acyclic, isEmpty_iff]
  intro n S
  exact IsEmpty.false (S.fₑ 0)

def loopless_of_acyclic {G : Graph V E} [Undirected G] (hGacyc : G.acyclic) : loopless G where
  no_loops e := by
    contrapose! hGacyc
    simp
    let v := G.v1 e
    use 1, ?_
    apply CycleGraph_SubgraphOf_of_isLoop (e := e) (i := v)
    rw [isLoop_iff_v1_eq_v2] at hGacyc
    simp only [inc_eq_undir_v12, hGacyc, v]

def simple_of_acyclic {G : Graph V E} [Undirected G] (hGacyc : G.acyclic) : Simple G where
  no_loops := (loopless_of_acyclic hGacyc).no_loops
  edge_symm := G.edge_symm
  inc_inj a b h := by
    by_contra! hab
    by_cases hloop : G.v1 a = G.v2 a
    · apply (loopless_of_acyclic hGacyc).no_loops a
      rwa [isLoop_iff_v1_eq_v2]
    · exact (hGacyc 2).false (CycleGraph_SubgraphOf_of_parallel G hab _ _ hloop h (inc_eq_undir_v12 a))

omit [DecidableEq V] in
lemma acyclic_of_loopless_Subsingleton_E {G : Graph V E} [loopless G] [Subsingleton E] :
    G.acyclic := by
  simp only [acyclic, isEmpty_iff]
  intro n S
  have := S.fₑinj <| Subsingleton.elim (S.fₑ 0) (S.fₑ 1)
  simp only [Fin.ext_iff', Fin.val_zero, Fin.val_one', Nat.Nat.zero_eq_one_mod_iff,
    PNat.coe_eq_one_iff] at this
  subst n
  apply G.no_loops (S.fₑ 0)
  rw [S.isLoop_iff, isLoop]
  have : (CycleGraph 1).inc 0 = undir s(0, 0) := by
    simp only [PNat.val_ofNat, CycleGraph, Fin.isValue, add_zero, Prod.mk_zero_zero]
  rw [this]; clear this
  simp only [PNat.val_ofNat, Fin.isValue, Prod.mk_zero_zero, undir_isFull,
    edge.isLoop_iff_v1_eq_v2, undir_v1, undir_v2, Fin.ext_iff', Fin.val_eq_zero]

omit [DecidableEq V] [DecidableEq W] in
lemma SubgraphOf.acyclic {G : Graph V E} {H : Graph W F} (hHG : H ⊆ᴳ G) :
    G.acyclic → H.acyclic := by
  intro hGacyclic n
  by_contra! h
  simp only [not_isEmpty_iff] at h
  obtain ⟨h⟩ := h
  specialize hGacyclic n
  apply hGacyclic.elim'
  exact h.trans hHG

-- lemma v12_not_conn_of_acyclic {G : Graph V E} [Undirected G] (hGacyc : G.acyclic) (e : E) :
--     ¬ (G{{e}ᶜ}ᴳ).conn (G.v1 e) (G.v2 e) := by
--   contrapose! hGacyc
--   obtain ⟨n, S, hs, ht⟩ := hGacyc.PathSubgraphOf
--   simp only [acyclic, not_forall, not_isEmpty_iff]
--   use n.succPNat
--   refine ⟨(CycleGraph_Isom_PathGraph_addUndirEdge n rfl).toSubgraphOf.trans ?_⟩
--   apply SubgraphOf.addUndirEdge (s(0, Fin.last n))
--     (S.trans (G.Es_spanningsubgraph {e}ᶜ).toSubgraphOf) (?_ : e ∉ _)
--   simp only [inc_eq_undir_v12, SubgraphOf.trans_fᵥ, Es_spanningsubgraph_fᵥ, CompTriple.comp_eq,
--     map_undir, Sym2.map_pair_eq, hs, ht]
--   simp only [SubgraphOf.trans_fₑ, Es_spanningsubgraph_fₑ, Set.mem_range, Function.comp_apply,
--     not_exists]
--   rintro i
--   exact (S.fₑ i).prop

lemma get_not_conn'_of_acyclic {G : Graph V E} [Undirected G] (hGacyc : G.acyclic) (e : E) :
    ¬ (G{{e}ᶜ}ᴳ).conn' (G.get e) := by
  rw [conn', ← lift_v12 (f := (G.Es {e}ᶜ).conn) (by simp only [conn_comm, implies_true])]
  contrapose! hGacyc
  obtain ⟨n, S, hs, ht⟩ := hGacyc.PathSubgraphOf
  simp only [acyclic, not_forall, not_isEmpty_iff]
  use n.succPNat
  refine ⟨(CycleGraph_Isom_PathGraph_addUndirEdge n rfl).toSubgraphOf.trans ?_⟩
  apply SubgraphOf.addUndirEdge (s(0, Fin.last n))
    (S.trans (G.Es_spanningsubgraph {e}ᶜ).toSubgraphOf) (?_ : e ∉ _)
  simp only [inc_eq_undir_v12, SubgraphOf.trans_fᵥ, Es_spanningsubgraph_fᵥ, CompTriple.comp_eq,
    map_undir, Sym2.map_pair_eq, hs, ht]
  simp only [SubgraphOf.trans_fₑ, Es_spanningsubgraph_fₑ, Set.mem_range, Function.comp_apply,
    not_exists]
  rintro i
  exact (S.fₑ i).prop

-- lemma v12_not_conn_iff_acyclic {G : Graph V E} [Undirected G] :
--     (∀ e, ¬ (G{{e}ᶜ}ᴳ).conn (G.v1 e) (G.v2 e)) ↔ G.acyclic := by
--   refine ⟨Function.mtr ?_, (v12_not_conn_of_acyclic ·)⟩
--   intro h
--   simp only [not_acyclic_iff_cycle, not_forall, not_not] at h ⊢
--   obtain ⟨n, S, _, _⟩ := h
--   use S.fₑ (-1)
--   rw [lift_v12 (f := (G.Es {S.fₑ (-1)}ᶜ).conn) (by simp only [conn_comm, implies_true]), Hom.get S]
--   apply SubgraphOf.conn' (S.Es_Es {-1}ᶜ {S.fₑ (-1)}ᶜ (fun e ⟨i, H2, H3⟩ ↦ by
--     simpa [S.fₑinj.eq_iff, ← H3] using H2))
--   simp only [CycleGraph_get, neg_add_cancel, conn'_pair]
--   convert ((CycleGraph.toPathGraph (PNat.natPred_add_one n).symm)).symm.toSubgraphOf.conn
--     ((PathGraph_conn_0 n.natPred (-1)).symm) <;> simp only [PNat.natPred, Fin.neg_one_eq_last,
--     CycleGraph_toPathGraph_symm_fᵥ, Fin.ext_iff', Fin.coe_neg_one', Fin.coe_cast, Fin.val_last,
--     Fin.val_zero]

lemma get_not_conn'_iff_acyclic {G : Graph V E} [Undirected G] :
    (∀ e, ¬ (G{{e}ᶜ}ᴳ).conn' (G.get e)) ↔ G.acyclic := by
  refine ⟨Function.mtr ?_, (get_not_conn'_of_acyclic ·)⟩
  intro h
  simp only [not_acyclic_iff_cycle, not_forall, not_not] at h ⊢
  obtain ⟨n, S, _, _⟩ := h
  use S.fₑ (-1)
  rw [Hom.get S]
  apply SubgraphOf.conn' (S.Es_Es {-1}ᶜ {S.fₑ (-1)}ᶜ (fun e ⟨i, H2, H3⟩ ↦ by
    simpa [S.fₑinj.eq_iff, ← H3] using H2))
  simp only [CycleGraph_get, neg_add_cancel, conn'_pair]
  convert ((CycleGraph.toPathGraph (PNat.natPred_add_one n).symm)).symm.toSubgraphOf.conn
    ((PathGraph_conn_0 n.natPred (-1)).symm) <;> simp only [PNat.natPred, Fin.neg_one_eq_last,
    CycleGraph_toPathGraph_symm_fᵥ, Fin.ext_iff', Fin.coe_neg_one', Fin.coe_cast, Fin.val_last,
    Fin.val_zero]

lemma get_not_conn'_iff_acyclic_of_Es_singleton_compl_acyclic {G : Graph V E} [Undirected G]
    (e : E) (hGe : G{{e}ᶜ}ᴳ.acyclic) : (¬ (G{{e}ᶜ}ᴳ).conn' (G.get e)) ↔ G.acyclic := by
  refine ⟨?_, (get_not_conn'_of_acyclic · e)⟩
  intro h n
  by_contra! h
  simp at h
  obtain ⟨S⟩ := h
  by_cases hS : e ∈ Set.range S.fₑ
  · obtain ⟨i, rfl⟩ := hS
    apply h; clear h
    rw [Hom.get]
    apply (S.Es_Es {i}ᶜ {S.fₑ i}ᶜ (by simp [S.fₑinj.eq_iff])).conn'
    convert CycleGraph_Es_singleton_eq_PathGraph (PNat.natPred_add_one n).symm i
      |>.symm.toSubgraphOf.conn' ((PathGraph n.natPred).all_conn'_get (s(-1, 0)))
    simp only [CycleGraph_get, CycleGraph_Es_singleton_eq_PathGraph, Isom.trans_symm, Isom.trans_fᵥ,
      Isom.Es_Es_symm_fᵥ, CycleGraph_rotate_symm_fᵥ, CycleGraph_toPathGraph_symm_fᵥ,
      Function.comp_apply, Sym2.map_pair_eq, Fin.cast_neg, Fin.cast_OfNat (i := 1), Fin.cast_zero,
      zero_sub, neg_sub, sub_neg_eq_add, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Fin.ext_iff',
      Prod.swap_prod_mk, self_eq_add_left, Fin.val_one', Fin.val_zero, Nat.one_mod_eq_zero_iff,
      PNat.coe_eq_one_iff]
    left
    ring_nf
    tauto
  · simp only [Set.mem_range, not_exists] at hS
    exact IsEmpty.false (self := hGe n) (S.Es {e}ᶜ (by simpa))

lemma NumberOfComponents_Es_eq_NumberOfComponents_iff (G : Graph V E) [Undirected G] (e : E) :
    (G.Es {e}ᶜ).connSetoid = G.connSetoid ↔ (G{{e}ᶜ}ᴳ).conn (G.v1 e) (G.v2 e) := by
  constructor <;> rintro h
  · simp only [Setoid.ext_iff, connSetoid] at h
    rw [h]
    apply conn.ofAdj <| adj_v12 G e
  · suffices Relation.ReflTransClosure (G.Es {e}ᶜ).adj = Relation.ReflTransClosure G.adj by
      simp only [connSetoid, conn, this]
    apply Relation.ReflTransClosure.closure_eq_closure_of_le_of_le_closure
    · rintro v w
      exact G.Es_spanningsubgraph {e}ᶜ |>.toSubgraphOf.adj
    · rintro v w hG
      change (G.Es {e}ᶜ).conn v w
      obtain ⟨f, hf⟩ := hG
      have := G.canGo_eq _ hf (G.canGo_v1_v2 f)
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := this
      · by_cases hef : f = e
        · subst e
          exact h
        · apply Relation.ReflTransGen.single
          use ⟨f, by simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hef, not_false_eq_true]⟩
          rw [← (G.Es_spanningsubgraph {e}ᶜ).canGo_iff]
          simp only [canGo, Es_spanningsubgraph_fᵥ, id_eq, Es_spanningsubgraph_fₑ, inc_eq_undir_v12,
            undir_canGo]
      · by_cases hef : f = e
        · subst e
          exact h.symm
        · apply Relation.ReflTransGen.single
          use ⟨f, by simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hef, not_false_eq_true]⟩
          rw [← (G.Es_spanningsubgraph {e}ᶜ).canGo_iff]
          simp only [canGo, Es_spanningsubgraph_fᵥ, id_eq, Es_spanningsubgraph_fₑ, inc_eq_undir_v12,
            canGo_iff_eq_of_undir, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
            or_true]

lemma c_lt_c_Es_of_acyclic [Fintype V] [Fintype E] {G : Graph V E}
    [Undirected G] (hG : G.acyclic) (e : E) :
    G.NumberOfComponents < (G.Es {e}ᶜ).NumberOfComponents := by
  unfold NumberOfComponents
  convert Quotient.card_quotient_lt_card_quotient_of_gt (?_ : _ < G.connSetoid)
  rw [lt_iff_le_and_ne]
  refine ⟨G.connSetoid_Es_le_connSetoid _, ?_⟩
  have h := get_not_conn'_of_acyclic hG e
  contrapose! h
  have : (G.Es {e}ᶜ).conn' (G.get e) ↔ G.connSetoid (G.v1 e) (G.v2 e) := by
    rw [← h]; simp only [get_eq_v12, conn'_pair, connSetoid]
  simp only [connSetoid] at this
  rw [this]; clear this h
  apply conn.ofAdj <| adj_v12 G e

theorem n_eq_m_add_c_of_acyclic [Fintype V] [Fintype E] {G : Graph V E} [Undirected G]
    (hG : G.acyclic) : Fintype.card V = Fintype.card E + NumberOfComponents G := by
  suffices ∀ m, Fintype.card E = m → Fintype.card V = m + NumberOfComponents G by refine this _ rfl
  rintro m
  induction' m with m ih generalizing E <;> rintro hm
  · rw [@Fintype.card_eq_zero_iff] at hm
    rw [NumberOfComponents_eq_card_V]
    omega
  · obtain e : E := by
      have : 0 < Fintype.card E := by omega
      rw [Fintype.card_pos_iff] at this
      exact this.some
    have := Fintype.ofFinite ({e}ᶜ : Set _).Elem
    have hm' : Fintype.card ({e}ᶜ : Set _).Elem = m := by
      rw [Fintype.card_compl_set, hm]
      simp only [Fintype.card_ofSubsingleton, add_tsub_cancel_right]
    have hG'Subgr := Es_spanningsubgraph G {e}ᶜ |>.toSubgraphOf
    have hG'Undir := hG'Subgr.Undirected'
    rw [ih (G := G{{e}ᶜ}ᴳ) (hG'Subgr.acyclic hG) hm']; clear hm ih
    suffices (G.Es {e}ᶜ).NumberOfComponents = 1 + G.NumberOfComponents by rw [this]; omega
    apply le_antisymm
    · unfold NumberOfComponents
      rw [add_comm, ← @Fintype.card_option]
      let f : Quotient (G.Es {e}ᶜ).connSetoid → Option (Quotient G.connSetoid) :=
        fun v ↦ by if h : v = ⟦G.v2 e⟧ then exact none
          else exact some (Quotient.idmap (G.connSetoid_Es_le_connSetoid _) v)
      convert Fintype.card_le_of_injective f ?_
      rintro v w h
      by_cases hv : v = ⟦G.v2 e⟧ <;> by_cases hw : w = ⟦G.v2 e⟧ <;> simp_all [f, dite_eq_ite,
        ite_false, Option.some.injEq]
      induction' v using Quotient.ind with v
      induction' w using Quotient.ind with w
      simp_all only [connSetoid, Quotient.eq, Quotient.idmap, Quotient.map'_mk'', id_eq]
      obtain ⟨n, S, hs, ht⟩ := h.PathSubgraphOf
      by_cases he : ∃ i, S.fₑ i = e
      · obtain ⟨i, hi⟩ := he
        have := S.canGo_iff (u := i.castSucc) (e := i) (v := i.succ) |>.mpr (PathGraph.canGo' i)
        simp only [canGo, inc_eq_undir_v12, canGo_iff_eq_of_undir, Sym2.eq, Sym2.rel_iff',
          Prod.mk.injEq, Prod.swap_prod_mk, hi] at this
        obtain ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩ := this
        · absurd hw; clear hv hw f hG'Subgr h
          have : (n - i.val.succ) + i.val.succ ≤ n := by omega
          let Sl := PathGraph_SubgraphOf_Pathgraph this
          have hslstart : Sl.fᵥ 0 = _ := PathGraph_SubgraphOf_Pathgraph_start this
          have hslend : Sl.fᵥ _ = _:= PathGraph_SubgraphOf_Pathgraph_end this
          have hnee: ∀ (e_1 : Fin (n - i.succ)), (Sl.trans S).fₑ e_1 ∈ ({e}ᶜ : Set _) := by
            rintro e'
            simp only [← hi, Nat.succ_eq_add_one, SubgraphOf.trans_fₑ, Function.comp_apply,
              Set.mem_compl_iff, Set.mem_singleton_iff]
            refine S.fₑinj.ne ?_
            simp only [Nat.succ_eq_add_one, PathGraph_SubgraphOf_Pathgraph_fₑapply,
              Fin.addNatEmb_apply, ← Fin.val_inj.ne, Fin.coe_castLE, Fin.coe_addNat, ne_eq, Sl]
            omega
          let Sl' := (Sl.trans S).Es {e}ᶜ hnee
          have hsl'fᵥ : Sl'.fᵥ = _ := (Sl.trans S).toHom.Es_fᵥ {e}ᶜ hnee |>.trans (Sl.trans_fᵥ S)
          rw [conn_comm]
          apply conn.OfPathSubgraphOf Sl' <;>
          simp only [Nat.succ_eq_add_one, hsl'fᵥ, Function.comp_apply, hslstart, hslend,
            Nat.cast_add, Fin.coe_eq_castSucc, Nat.cast_one, Fin.coeSucc_eq_succ, ← ht,
            S.fᵥinj.eq_iff, hv2]
          simp only [Fin.natCast_eq_last, ← Fin.val_inj, Fin.val_add, Fin.val_natCast, Fin.val_succ,
            Nat.mod_add_mod, Fin.val_last]
          rw [Nat.sub_add_cancel (by omega), Nat.mod_succ]
        · absurd hv
          have : i.val + 0 ≤ n := by omega
          let Sp := PathGraph_SubgraphOf_Pathgraph this
          have hspstart : Sp.fᵥ 0 = 0 := PathGraph_SubgraphOf_Pathgraph_start this
          have hspend : Sp.fᵥ _ = _ := PathGraph_SubgraphOf_Pathgraph_end this
          have hnee: ∀ (e_1 : Fin i), (Sp.trans S).fₑ e_1 ∈ ({e}ᶜ : Set E) := by
            rintro e'
            simp only [← hi, Nat.succ_eq_add_one, SubgraphOf.trans_fₑ, Function.comp_apply,
              Set.mem_compl_iff, Set.mem_singleton_iff]
            refine S.fₑinj.ne ?_
            rw [PathGraph_SubgraphOf_Pathgraph_fₑapply, ← Fin.val_inj.ne]
            simp only [Nat.add_zero, Fin.coe_castLE, ne_eq]
            omega
          let Sp' := (Sp.trans S).Es {e}ᶜ hnee
          have hsp'fᵥ : Sp'.fᵥ = _ := (Sp.trans S).toHom.Es_fᵥ {e}ᶜ hnee |>.trans (Sp.trans_fᵥ S)
          apply conn.OfPathSubgraphOf Sp' <;>
          simp only [Nat.succ_eq_add_one, hsp'fᵥ, Function.comp_apply, hspstart, hspend,
            Fin.coe_eq_castSucc, Nat.cast_one, Fin.coeSucc_eq_succ, ← hs, S.fᵥinj.eq_iff, hv2]
          simp only [add_zero, Fin.coe_eq_castSucc]
      save
      · simp only [not_exists] at he
        have : ∀ (e_1 : Fin n), S.fₑ e_1 ∈ ({e}ᶜ : Set E) := by
          rintro e'
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff, he, not_false_eq_true]
        let S' := S.Es {e}ᶜ this
        have hfᵥ : S'.fᵥ = _ := S.Es_fᵥ {e}ᶜ this
        apply conn.OfPathSubgraphOf S' <;> simp only [hfᵥ, ← hs, Fin.natCast_eq_last, ← ht]
    · suffices G.NumberOfComponents < (G.Es {e}ᶜ).NumberOfComponents by omega
      convert c_lt_c_Es_of_acyclic hG e

#print axioms n_eq_m_add_c_of_acyclic

lemma acyclic_of_Es_acyclic_of_Es_subset {G : Graph V E} [Undirected G] {A B : Set E}
    (hAacyc : (G.Es A).acyclic) (hAFin : A.Finite) (hBacyc : (G.Es B).acyclic) (hBFin : B.Finite)
    (hAltB : A.ncard < B.ncard) : ¬(G.Es B).conn ≤ (G.Es A).conn := by
  rintro h
  let S := G.incEsV (A ∪ B)
  let GB := (G.EVSubgraph S B sorry)
  let GA := (G.EVSubgraph S A sorry)
  have hSfin : Fintype S.Elem := sorry
  have hBfin : Fintype B.Elem := hBFin.fintype
  have hAfin : Fintype A.Elem := hAFin.fintype
  have hAcardltBcard : Fintype.card A < Fintype.card B := by
    convert hAltB
    · rw [← Set.Finite.card_toFinset hAFin]
      exact (Set.ncard_eq_toFinset_card A hAFin).symm
    · rw [← Set.Finite.card_toFinset hBFin]
      exact (Set.ncard_eq_toFinset_card B hBFin).symm
  have hGBundir : GB.Undirected := G.EVSubgraphOf S B sorry |>.Undirected'
  have hGAundir : GA.Undirected := G.EVSubgraphOf S A sorry |>.Undirected'
  have hGBacyc : GB.acyclic := sorry
    -- (G{B}ᴳ).Vs_subgraph S |>.acyclic hBacyc
  have hGAacyc : GA.acyclic := sorry
  have hGBconnleGAconn : GB.conn ≤ GA.conn := sorry
  have : GA.NumberOfComponents ≤ GB.NumberOfComponents := sorry
  have := (n_eq_m_add_c_of_acyclic hGAacyc).symm.trans (n_eq_m_add_c_of_acyclic hGBacyc)
  omega

-- theorem n_eq_m_add_c_iff_acyclic [Fintype V] [Fintype E] {G : Graph V E} [Undirected G] :
--     Fintype.card V = Fintype.card E + NumberOfComponents G ↔ G.acyclic := by
--   refine ⟨?_, n_eq_m_add_c_of_acyclic⟩
--   intro h

structure Forest (V E : Type*) [DecidableEq V] extends Graph V E where
  no_cycle : IsEmpty toGraph.Cycle

structure Tree (V E : Type*) [DecidableEq V] extends Forest V E where
  conn : toGraph.connected

instance instTreeConnected (T : Tree V E) : T.connected := T.conn

def EdgelessForest (n : ℕ) : Forest (Fin n) Empty where
  toGraph := EdgelessGraph (Fin n)
  no_cycle := by
    by_contra!
    simp only [not_isEmpty_iff] at this
    obtain ⟨C, hCvNod, hCeNod, hCeNonempty⟩ := this
    obtain e := C.edges.head hCeNonempty
    exact e.elim

def PathTree (n : ℕ) : Tree (Fin (n+1)) (Fin n) where
  toGraph := PathGraph n
  no_cycle := by
  -- get a Cycle then vertices of the cycle as to be monotone increasing or decreaseing
  -- but C.start = C.finish so C.edges  = []
  -- contradiction
    sorry
  conn := inferInstance


lemma existSpanningTree_aux [Fintype V] (G : Graph V E) [G.connected] :
    Fintype.card V = n → ∃ (W F : Type) (h : DecidableEq W) (T : Tree W F),
    Nonempty (T.SpanningSubgraphOf G) := by
  by_cases h : n = 0
  · rintro rfl
    use Fin 0, Empty, inferInstance, ⟨EdgelessForest 0, @instEdgelessGraphConnected _ ⟨by omega⟩⟩
    refine ⟨⟨⟨Fin.elim0 , Empty.elim, (Empty.elim ·)⟩, (Fin.elim0 ·), (Empty.elim ·)⟩, fun v => ?_⟩
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp h
    exact this.elim v
  have hn : 1 ≤ n := by omega
  induction hn using Nat.leRec generalizing V E with
  | refl =>
    rintro hn
    use (Fin 1), Empty, inferInstance, ⟨EdgelessForest 1, @instEdgelessGraphConnected _ ⟨by omega⟩⟩
    refine ⟨⟨⟨?_, Empty.elim, (Empty.elim ·)⟩, ?_, (Empty.elim ·)⟩, ?_⟩
    · choose x hx using Fintype.card_eq_one_iff.mp hn
      exact fun v => x
    · rintro u v h
      exact Subsingleton.allEq u v
    · rintro v
      simp only [exists_const]
      have := Fintype.card_le_one_iff_subsingleton.mp (by rw [hn])
      exact Subsingleton.allEq _ v
  | le_succ_of_le n ih =>
    rintro hn
    rename_i a b _ _ _
    have hVNonempty : Nonempty V := by
      rw [← Fintype.card_pos_iff]
      omega
    obtain ⟨v⟩ := hVNonempty
    let G' := G[{v}ᶜ]ᴳ
    have hG'conn : G'.connected := by sorry
    have hG'Vcard : Fintype.card ({v}ᶜ : Set V) = b := by sorry
    obtain ⟨T, ⟨hT⟩⟩ := ih G' (Nat.not_eq_zero_of_lt n) hG'Vcard
    have hV'Nonempty : Nonempty ({v}ᶜ : Set V) := by sorry
    obtain ⟨u, hu⟩ := hV'Nonempty
    have huvConn : G.conn u v := connected.all_conn u v
    obtain ⟨P, hPstart, hPfinish⟩ := huvConn.path
    have huNev : u ≠ v := by simpa only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff] using hu
    have hPlenpos := P.length_pos_of_start_ne_finish (hPstart ▸ hPfinish ▸ huNev)
    have hPlen : P.vertices.tail ≠ [] := by sorry
    let w := P.vertices.tail.head hPlen
    let e := P.edges.head sorry
    sorry
