import Kura.Conn.closedWalk
import Kura.Conn.Conn
import Kura.Examples.Conn
import Kura.Graph.Remove

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W]


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
    use Fin 0, Empty, inferInstance, ⟨EdgelessForest 0, ?_⟩
    · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · refine ⟨?_, ?_⟩
        · rintro e
          exact Fin.elim0 e
        · rintro i j h
          exact Subsingleton.elim i j
      · refine ⟨?_, ?_⟩
        · rintro e
          exact e.elim
        · exact Function.injective_of_subsingleton _
      · rintro e
        exact e.elim
      · rintro e
        simp only [IsEmpty.exists_iff]
        have : IsEmpty V := by exact Fintype.card_eq_zero_iff.mp h
        exact IsEmpty.false e
    refine ⟨?_⟩
    rintro u v
    exact u.elim0
  have hn : 1 ≤ n := by omega
  induction hn using Nat.leRec generalizing V E with
  | refl =>
    rintro hn
    use (Fin 1)
    use Empty
    use inferInstance
    use ⟨EdgelessForest 1, ?_⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · refine ⟨?_, ?_⟩
      · rintro e
        have hVNonempty : Nonempty V := sorry
        obtain v := hVNonempty.some
        exact v
      · rintro i j
        simp only [forall_const]
        exact Subsingleton.elim i j
    · refine ⟨?_, ?_⟩
      · rintro e
        exact e.elim
      · exact Function.injective_of_subsingleton _
    · rintro e
      exact e.elim
    · sorry
    · sorry
  | le_succ_of_le n ih =>
    rintro hn
    rename_i a b _ _ _
    have hVNonempty : Nonempty V := by sorry
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
