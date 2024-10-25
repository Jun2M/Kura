import Kura.Conn.Walk
import Kura.Graph.Remove
import Kura.Dep.Rel
import Kura.Graph.Searchable


namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] (G : Graph V E)


def conn : V → V → Prop := Relation.ReflTransClosure G.adj

@[simp]
lemma conn_refl (v : V) : G.conn v v := Relation.ReflTransGen.refl

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


instance instConnDec [Fintype V] [G.SearchableOut]: DecidableRel G.conn :=
  Relation.ReflTransGenDeciable

class connected : Prop where
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

lemma conn.SubgraphOf {G : Graph V E} {H : Graph W F} (h : G ⊆ᴳ H) {u v : V} (huv : G.conn u v) :
    H.conn (h.fᵥ u) (h.fᵥ v) := by
  induction huv with
  | refl => exact conn_refl _ _
  | tail _h1 h2 IH => exact IH.tail (h.adj G H _ _ h2)

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

lemma NumberOfComponents_eq_card_V [Fintype V] [IsEmpty E] [Fintype E] [Undirected G] :
    G.NumberOfComponents = Fintype.card V := by
  sorry

lemma NumberOfComponents_eq_one [Fintype V] [Fintype E] [Undirected G] [G.connected] :
    G.NumberOfComponents = 1 := by
  sorry

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

def edgeCut' (S : Set E) : Prop :=
  ∃ u v, G.conn u v ∧ ∀ w : Walk G, w.start = u ∧ w.finish = v → ∃ e ∈ S, e ∈ w.edges

@[simp]
def edgeCut [DecidableEq E] (S : Finset E) : Prop := ∃ u v, G.conn u v ∧ ¬ G{Sᶜ}ᴳ.conn u v

lemma edgeCut_of_not_conn [DecidableEq E] (S : Finset E) (u v : V) (hG : G.conn u v)
  (hGS : ¬ G{Sᶜ}ᴳ.conn u v) : G.edgeCut S := ⟨ u, v, hG, hGS ⟩

lemma empty_not_edgeCut [DecidableEq E]: ¬ G.edgeCut ∅ := by
  rintro ⟨ u', v', hG', hGS ⟩
  -- Isom theorems...
  sorry

lemma edgeCut_upward_closed [DecidableEq E] (S T : Finset E) (hST : S ⊆ T) (hCut : G.edgeCut S) :
     G.edgeCut T := by
  unfold edgeCut at hCut ⊢
  contrapose! hCut
  intro u v hG
  obtain ⟨P, hPstart, hPfinish⟩ := (hCut u v hG).path
  obtain ⟨P', hP'start, hP'finish⟩ : ∃ P' : (G.Es Sᶜ).Path, P'.start = u ∧ P'.finish = v := by
    -- Subtype theorems...
    sorry
  rw [← hP'start, ← hP'finish]
  exact conn.ofPath _ P'

def bridge [DecidableEq E] (e : E) : Prop := G.connected ∧ G.edgeCut {e}

def minEdgeCut [DecidableEq E] (S : Finset E) : Prop :=
  Minimal (G.edgeCut ·) S

lemma edgeCut_of_minEdgeCut [DecidableEq E] (S : Finset E) (h : G.minEdgeCut S) : G.edgeCut S := by
  unfold minEdgeCut Minimal at h
  exact h.1

lemma empty_not_minEdgeCut [DecidableEq E] : ¬ G.minEdgeCut ∅ := by
  rintro ⟨ hCut, _hMin ⟩
  exact empty_not_edgeCut _ hCut

-- def isolatingEdgeCut [DecidableEq E] [Searchable G] (v : V) := G.incEdges v

lemma incEdges_edgeCut (v : V) [Nontrivial V] [DecidableEq E] [Searchable G] :
    G.edgeCut (G.incEdges v) := by
  simp only [edgeCut]
  obtain ⟨w, hw⟩ := exists_ne v
  sorry

lemma bridge_minEdgeCut [DecidableEq E] (e: E) (h: G.bridge e) :
    G.minEdgeCut {e} := by
  unfold minEdgeCut Minimal
  obtain ⟨ _, hCut⟩ := h
  refine ⟨ hCut, ?_ ⟩
  rintro S hS Sle
  simp_all only [Finset.le_eq_subset, Finset.subset_singleton_iff, Finset.singleton_subset_iff]
  obtain hS | hS := Sle <;> subst hS
  · unfold edgeCut at hS
    absurd hS
    push_neg
    intro u v hG
    sorry
    -- requires some Isom theorems
  · simp only [Finset.mem_singleton]


class NEdgeConnected [DecidableEq E] (n : ℕ) : Prop :=
  all_conn : ∀ u v : V, conn G u v
  no_small_cut : ∀ S : Finset E, S.card < n → ¬ G.edgeCut S

def ball (u : V) (n : ℕ) : Set V :=
  {v | ∃ w : Walk G, w.start = u ∧ w.length ≤ n ∧ w.finish = v}

class NConnected [Fintype V] [fullGraph G] (n : ℕ) : Prop where
  h : ∀ S : Finset V, S.card ≤ n → G[Sᶜ]ᴳ.connected
