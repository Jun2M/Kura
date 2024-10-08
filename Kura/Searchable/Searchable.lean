import Kura.Graph.Undirected
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.OpClass


namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E) (e : E) (u v w : V)

-- There is a finset of edges that leads out of a vertex
class SearchableOut where
  outEdges : V → Finset E
  mem_outEdges : ∀ v e, e ∈ outEdges v ↔ v ∈ G.startAt e


def outEdges [SearchableOut G] (v : V) : Finset E := SearchableOut.outEdges G v

@[simp]
lemma mem_outEdges [SearchableOut G] : e ∈ G.outEdges v ↔ v ∈ G.startAt e := by
  rw [← SearchableOut.mem_outEdges (G := G) v e]
  rfl

-- Rethink about how to define this again
-- def outNeighbors [SearchableOut G] : Multiset V := (G.outEdges v |>.val |>.map (G.gofrom? v ·)).eraseNone
-- def outDegree [SearchableOut G] : ℕ := Multiset.card (G.outNeighbors v)

lemma mem_outEdges_iff_mem_get [Undirected G] [SearchableOut G] : e ∈ G.outEdges v ↔ v ∈ G.get e := by
  rw [mem_outEdges]
  simp only [startAt, inc_eq_undir_get, mem_startAt_undir]

-- There is a finset of edges that leads into a vertex
class SearchableIn where
  inEdges : V → Finset E
  mem_inEdges : ∀ v e, e ∈ inEdges v ↔ v ∈ G.finishAt e


def inEdges [SearchableIn G] (v : V) : Finset E := SearchableIn.inEdges G v

@[simp]
lemma mem_inEdges [SearchableIn G] : e ∈ G.inEdges v ↔ v ∈ G.finishAt e := by
  rw [← SearchableIn.mem_inEdges (G := G) v e]
  rfl

-- def inNeighbors [SearchableIn G] : Multiset V := (G.inEdges v |>.val |>.map (G.gofrom? v ·)).eraseNone
-- def inDegree [SearchableIn G] : ℕ := Multiset.card (G.inNeighbors v)


-- There is a finset of edges that are incident to a vertex
class Searchable extends SearchableOut G, SearchableIn G where

variable [Searchable G] [DecidableEq E]

def incEdges : Finset E := G.outEdges v ∪ G.inEdges v
def neighbors  : Multiset V :=
  G.outEdges v ∪ G.inEdges v |>.val |>.map (G.endAt ·) |>.foldl (· + ·) ∅ |>.filter (· ≠ v)
def degree : ℕ :=
  G.outEdges v ∪ G.inEdges v |>.val |>.map (G.endAt ·) |>.foldl (· + ·) ∅ |>.count v
-- Deliverately double counts loops

lemma incEdges_card_eq_degree [G.loopless] : (G.incEdges v).card = G.degree v := by
  sorry

@[simp]
lemma incEdges_eq_outEdges [G.Undirected] : G.incEdges v = G.outEdges v := by
  sorry



def regular (k : ℕ) : Prop := ∀ v : V, G.degree v = k

instance instRegularDecidablePred : DecidablePred (G.regular ·) := by
  sorry

instance DecidableRelAdjOfFintypeE [Searchable G] : DecidableRel (G.adj : V → V → Prop) := by
  intro u v
  apply decidable_of_iff (G.outEdges u |>.filter (G.canGo u · v)).Nonempty
  simp only [Finset.Nonempty, canGo, Finset.mem_filter, mem_outEdges, startAt, adj]
  apply exists_congr
  intro e
  apply and_iff_right_of_imp
  intro h
  exact mem_startAt_of_canGo _ _ _ h
