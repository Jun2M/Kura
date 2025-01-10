import Kura.Connectivity.closedWalk
import Kura.Connectivity.Conn
import Kura.Examples.Conn
import Kura.Graph.Remove

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W]


def acyclic (G : Graph V E) : Prop := ∀ n, IsEmpty <| TourGraph n ⊆ᴳ G

omit [DecidableEq V] [DecidableEq W] in
lemma SubgraphOf.acyclic {G : Graph V E} {H : Graph W F} (hHG : H ⊆ᴳ G) : G.acyclic → H.acyclic := by
  intro hGacyclic n
  by_contra! h
  simp only [not_isEmpty_iff] at h
  obtain ⟨h⟩ := h
  specialize hGacyclic n
  apply hGacyclic.elim'
  exact h.trans hHG

lemma endAt_not_conn {G : Graph V E} [Undirected G] (hGacyc : G.acyclic) (e : E) :
    ¬ G.conn (G.v1 e) (G.v2 e) := by
  rintro hconn
  

theorem n_eq_m_add_c_of_acyclic [Fintype V] [Fintype E] {G : Graph V E} [Undirected G]
    (hG : G.acyclic) : Fintype.card V = Fintype.card E + NumberOfComponents G := by
  suffices ∀ m, Fintype.card E = m → Fintype.card V = m + NumberOfComponents G by
    refine this _ rfl
  rintro m
  induction' m with m ih generalizing E <;> rintro hm
  · rw [@Fintype.card_eq_zero_iff] at hm
    rw [NumberOfComponents_eq_card_V]
    omega
  · obtain e : E := by
      have : 0 < Fintype.card E := by omega
      rw [Fintype.card_pos_iff] at this
      exact this.some
    let E' := ({e}ᶜ : Set _).Elem
    have : Fintype E' := Fintype.ofFinite E'
    have hG'Subgr := Es_spanningsubgraph G {e}ᶜ |>.toSubgraphOf
    have hG'Undir := Es_spanningsubgraph G {e}ᶜ |>.toSubgraphOf.Undirected
    specialize ih (G := G{{e}ᶜ}ᴳ) (hG'Subgr.acyclic hG) ?_
    · rw [Fintype.card_compl_set, hm]
      simp only [Fintype.card_ofSubsingleton, add_tsub_cancel_right]
    rw [ih]
    suffices (G.Es {e}ᶜ).NumberOfComponents = 1 + G.NumberOfComponents by rw [this]; omega

    sorry

structure Forest (V E : Type*) [DecidableEq V] extends Graph V E where
  no_cycle : IsEmpty toGraph.Cycle

structure Tree (V E : Type*) [DecidableEq V] extends Forest V E where
  conn : toGraph.connected

instance instTreeConnected (T : Tree V E) : T.connected := T.conn

def EdgelessForest (n : ℕ) : Forest (Fin n) Empty where
  toGraph := EdgelessGraph n
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
