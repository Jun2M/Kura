import Kura.Graph.Edges
import Kura.Dep.Embedding



@[ext]
structure Graph (V E : Type*) [LinearOrder V] where
  inc : E → edge V

namespace Graph
open edge
variable {U V W E F E' : Type*} [LinearOrder U] [LinearOrder V] [LinearOrder W] (G : Graph V E)
  (e e' : E) (u v w : V)

def toEdgeMultiset [Fintype E] : Multiset (edge V) :=
  (@Fintype.elems E _ : Finset E)
  |>.val
  |>.map G.inc

unsafe instance [Repr V] [Fintype E] : Repr (Graph V E) where
  reprPrec G _ := "Graph " ++ repr G.toEdgeMultiset

/- Carry the defs from Edges to Graph -/
@[simp] abbrev isDir : Bool := (G.inc e).isDir
@[simp] abbrev isUndir : Bool := (G.inc e).isUndir
@[simp] abbrev isFull : Bool := (G.inc e).isFull
@[simp] abbrev isHalf : Bool := (G.inc e).isHalf
@[simp] abbrev isFree : Bool := (G.inc e).isFree
@[simp] abbrev isLoop : Bool := (G.inc e).isLoop
@[simp] abbrev isArc : Bool := (G.inc e).isArc
@[simp] abbrev endAt : Multiset V := (G.inc e).endAt
@[simp] abbrev startAt : Multiset V := (G.inc e).startAt
@[simp] abbrev finishAt : Multiset V := (G.inc e).finishAt
@[simp] abbrev gofrom? (v : V) (e : E): Option V := (G.inc e).gofrom? v
@[simp] abbrev goback? (v : V) (e : E) : Option V := (G.inc e).goback? v
@[simp] abbrev canGo (v : V) (e : E) (w : V) : Bool := (G.inc e).canGo v w
@[simp] abbrev flip : edge V := (G.inc e).flip
@[simp] abbrev any := (G.inc e).any
@[simp] abbrev all := (G.inc e).all


/-- A full graph is one with no half-edges.-/
class fullGraph : Prop :=
  all_full : ∀ e, G.isFull e

/-- An undirected graph is a full graph with no arcs -/
class Undirected extends fullGraph G : Prop :=
  edge_symm : ∀ e, G.isUndir e

/-- A loopless graph is one with no loops, free edges or half_edges
  (so every edge is an arc or edge ) -/
class loopless extends fullGraph G : Prop :=
  no_loops : ∀ e, ¬G.isLoop e


/-- A simple graph is one where every edge is a actual undirected 'edge'
  and no two edges have the same ends.  -/
class Simple extends loopless G, Undirected G : Prop :=
  inc_inj : G.inc.Injective

class Directed extends fullGraph G : Prop :=
  no_undir : ∀ e, ¬G.isUndir e


lemma all_full [fullGraph G] : ∀ e, G.isFull e := fullGraph.all_full
lemma no_undir [Directed G] : ∀ e, ¬G.isUndir e := Directed.no_undir
lemma edge_symm [Undirected G] : ∀ e, G.isUndir e := Undirected.edge_symm
lemma no_loops [loopless G] : ∀ e, ¬G.isLoop e := loopless.no_loops
lemma inc_inj [Simple G] : G.inc.Injective := Simple.inc_inj


/- Basic functions -/
-- def split : Multiset (Option V × E × Option V) := match G.inc e with
--   | dir p => {(p.fst, e, p.snd)}
--   | undir s => {(some s.inf, e, some s.sup), (some s.sup, e, some s.inf)}

def incEV := λ e => {v | v ∈ G.inc e}
def incVE := λ v => {e | v ∈ G.startAt e}
def incVV := λ v => {u | ∃ e, u ≠ v ∧ u ∈ G.inc e ∧ v ∈ G.inc e}
def incEE := λ e => {e' | (e = e' ∧ G.isLoop e) ∨ (e ≠ e' ∧ G.startAt e ∩ G.finishAt e' ≠ ∅)}

lemma loop_mem_incEE (hloop : G.isLoop e) : e ∈ G.incEE e := by
  simp only [incEE, Set.mem_setOf_eq, true_and]
  exact Or.inl hloop

lemma ne_of_mem_incEE_of_notLoop (h : e' ∈ G.incEE e) (hloop : ¬G.isLoop e) : e ≠ e' := by
  rintro rfl
  simp only [incEE, isLoop, ne_eq, startAt, finishAt, Multiset.empty_eq_zero, Set.mem_setOf_eq,
    true_and, not_true_eq_false, false_and, or_false] at h
  exact hloop h

def adj : Prop := ∃ e, G.canGo u e v
def neighbourhood : Set V := {u | G.adj u v}

macro u:term "—[" e:term "]—" v:term : term => `(G.canGo $u $e $v)


variable (H : Graph W F) (I : Graph U E')

structure Hom where
  fᵥ : V → W
  fₑ : E → F
  comm : ∀ e, H.inc (fₑ e) = (G.inc e).map fᵥ

def Hom.inj (a : Hom G H) : Prop := a.fᵥ.Injective ∧ a.fₑ.Injective

def Hom.surj (a : Hom G H) : Prop := a.fᵥ.Surjective ∧ a.fₑ.Surjective

structure SubgraphOf where
  fᵥ : V ↪ W
  fₑ : E ↪ F
  comm : ∀ e, H.inc (fₑ e) = (G.inc e).map fᵥ

macro G:term "⊆ᴳ" H:term :term => `(Graph.SubgraphOf $G $H)

unsafe instance [Repr W] [Repr V] [Fintype E] [Fintype F] : Repr (G ⊆ᴳ H) where
  reprPrec _SubgraphOf _ := repr G ++ " ⊆ᴳ " ++ repr H

def SubgraphOf.refl : G ⊆ᴳ G := ⟨Function.Embedding.refl V, Function.Embedding.refl E,
  fun _ => (map_id _).symm ⟩

def SubgraphOf.trans {G : Graph V E} {H : Graph W F} {I : Graph U E'} (a : G ⊆ᴳ H) (b : H ⊆ᴳ I) :
    G ⊆ᴳ I where
  fᵥ := a.fᵥ.trans b.fᵥ
  fₑ := a.fₑ.trans b.fₑ
  comm e := by
    simp only [Function.Embedding.trans_apply, b.comm, map, a.comm]
    exact (map_comp a.fᵥ b.fᵥ (G.inc e)).symm

lemma SubgraphOf.CanGo (A : G ⊆ᴳ H) (u v : V) (e : E) :
    G.canGo u e v → H.canGo (A.fᵥ u) (A.fₑ e) (A.fᵥ v) := by
  intro h
  simpa only [canGo, A.comm, map_canGo]

lemma SubgraphOf.adj (A : G ⊆ᴳ H) (u v : V) : G.adj u v → H.adj (A.fᵥ u) (A.fᵥ v) := by
  intro h
  obtain ⟨e, he⟩ := h
  exact ⟨A.fₑ e, A.CanGo _ _ u v e he⟩

noncomputable def SubgraphOf.FintypeV [Fintype W] (A : G ⊆ᴳ H) : Fintype V := by
  exact Fintype.ofInjective A.fᵥ A.fᵥ.inj'

noncomputable def SubgraphOf.FintypeE [Fintype F] (A : G ⊆ᴳ H) : Fintype E := by
  exact Fintype.ofInjective A.fₑ A.fₑ.inj'

structure Isom where
  toSubgraphOf : G ⊆ᴳ H
  invSubgraphOf : H ⊆ᴳ G

macro G:term "≃ᴳ" H:term :term => `(Graph.Isom $G $H)

def Isom.refl : G ≃ᴳ G := ⟨SubgraphOf.refl G, SubgraphOf.refl G⟩

def Isom.symm (A : G ≃ᴳ H) : H ≃ᴳ G := ⟨A.invSubgraphOf, A.toSubgraphOf⟩

def Isom.trans (A₁ : G ≃ᴳ H) (A₂ : H ≃ᴳ I) : G ≃ᴳ I :=
  ⟨A₁.toSubgraphOf.trans A₂.toSubgraphOf, A₂.invSubgraphOf.trans A₁.invSubgraphOf⟩


end Graph
