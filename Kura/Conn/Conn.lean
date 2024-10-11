import Kura.Conn.Walk
import Kura.Graph.Subgraph
import Kura.Searchable.Finite
import Kura.Dep.Rel


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E)


def conn : V → V → Prop := Relation.ReflTransGen G.adj

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


class connected : Prop where
  all_conn : ∀ u v : V, conn G u v

def all_conn (u v : V) [G.connected] : conn G u v := connected.all_conn u v

def connSetoid [Undirected G] : Setoid V where
  r := conn G
  iseqv := by
    refine ⟨ ?_, ?_, ?_ ⟩
    · intro a
      exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.symmetric
      intro x y hxy
      exact (G.adj_symmetric x y).mp hxy
    · intro a b c hab hbc
      exact Relation.ReflTransGen.trans hab hbc

def NumberOfComponents [Fintype V] [Searchable G] [Undirected G] : ℕ :=
  @Fintype.card (Quotient (connSetoid G)) (@Quotient.fintype V _ (connSetoid G) (Relation.ReflTransGenDeciable))

lemma NumberOfComponents_le_card_V [Fintype V] [Fintype E] [Undirected G] :
    G.NumberOfComponents ≤ Fintype.card V := by
  unfold NumberOfComponents
  exact @Fintype.card_quotient_le V _ G.connSetoid Relation.ReflTransGenDeciable

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

def edgeCut (S : Set E) : Prop :=
  ∃ u v, G.conn u v ∧ ∀ w : Walk G, w.start = u ∧ w.finish = v → ∃ e ∈ S, e ∈ w.edges

def edgeCut' (S : Set E) [DecidablePred (· ∈ S)] : Prop :=
  ¬(G.deleteEdges S).eval.connected


def bridge (e : E) : Prop := G.edgeCut {e}

def minEdgeCut (S : Set E) : Prop :=
  Minimal (G.edgeCut ·) S

def isolatingEdgeCut (v : V) : Set E := {e | v ∈ G.endAt e}

lemma isolatingEdgeCut_is_edgeCut (v : V) [Nontrivial V] : G.edgeCut (G.isolatingEdgeCut v) := by
  simp [isolatingEdgeCut, edgeCut]
  obtain ⟨w, hw⟩ := exists_ne v

  sorry

lemma bridge_is_minEdgeCut (e: E) (h: G.bridge e) : G.minEdgeCut {e} := by
  unfold minEdgeCut Minimal
  constructor
  · simp only
    exact h
  · rintro S hS Sle
    simp_all only [Set.le_eq_subset, Set.subset_singleton_iff, Set.singleton_subset_iff]
    obtain ⟨u,v,hconn,hwalk⟩ := hS
    obtain ⟨P, hpath⟩ := hconn.path
    obtain ⟨f, fS, _⟩  := hwalk P.toWalk hpath
    obtain rfl := Sle f fS
    exact fS

def ball (u : V) (n : ℕ) : Set V :=
  {v | ∃ w : Walk G, w.start = u ∧ w.length ≤ n ∧ w.finish = v}
