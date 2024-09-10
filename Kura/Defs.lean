import Kura.Edges
import Kura.Dep.Biggest


@[ext]
structure Graph (V E : Type*) [DecidableEq V] where
  inc : E → edge V

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] (G : Graph V E) (e : E) (u v w : V)


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
@[simp] abbrev gofrom (v : V) : Multiset V := (G.inc e).gofrom v
@[simp] abbrev gofrom? (v : V) : Option V := (G.inc e).gofrom? v
@[simp] abbrev goback? (v : V) : Option V := (G.inc e).goback? v
@[simp] abbrev canGo (v : V) (e : E) (w : V) : Bool := (G.inc e).canGo v w
@[simp] abbrev flip : edge V := (G.inc e).flip
@[simp] abbrev map (f : V → W) : edge W := (G.inc e).map f
@[simp] abbrev pmap {P : V → Prop} (f : ∀ a, P a → W) (e : E) :
  (∀ v ∈ G.inc e, P v) → edge W := ((G.inc e).pmap f ·)

/-- A full graph is one with no half-edges.-/
class fullGraph : Prop :=
  all_full : ∀ e, G.isFull e

/-- An undirected graph is a full graph with no arcs -/
class undirected extends fullGraph G :=
  edge_symm : ∀ e, G.isUndir e

/-- A loopless graph is one with no loops, free edges or half_edges
  (so every edge is an arc or edge ) -/
class loopless extends fullGraph G :=
  no_loops : ∀ e, ¬G.isLoop e

/-- A simple graph is one where every edge is a actual undirected 'edge'
  and no two edges have the same ends.  -/
class simple extends loopless G, undirected G :=
  inc_inj : G.inc.Injective


lemma exist_Sym2 [undirected G] : ∃ s, G.inc e = undir s := by
  match h : G.inc e with
  | dir (a, b) =>
    have := @undirected.edge_symm _ _ _ G _ e
    cases a <;> cases b <;> simp_all
  | undir s => exact ⟨s, rfl⟩

lemma fullGraph.no_free [fullGraph G] : ∀ e, ¬ G.isFree e := by
  intro e
  have := @fullGraph.all_full _ _ _ G _ e
  match h : G.inc e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all
  | undir s =>
    simp_all

lemma endAt_ne_zero [fullGraph G] : G.endAt e ≠ 0 := by
  intro h
  match he : G.inc e with
  | dir (a, b) =>
    cases a <;> cases b <;> simp_all
    apply @fullGraph.no_free _ _ _ G _ e
    simp [he]
  | undir s =>
    simp_all only [endAt, edge.endAt]
    apply_fun Multiset.card at h
    rw [Sym2.toMultiset_card s] at h
    simp at h

@[simp]
lemma not_dir_none_none [fullGraph G] : G.inc e ≠ dir (none, none) := by
  intro h
  apply @fullGraph.no_free _ _ _ G _ e
  simp [h]

-- lemma

lemma exist_mem [fullGraph G] : ∃ v, v ∈ G.inc e := Multiset.exists_mem_of_ne_zero (endAt_ne_zero G e)


def adj : Prop := ∃ e, G.canGo u e v

def neighbourhood : Set V := {u | G.adj u v}

def inNeighbors [Fintype E] : Multiset V :=
  @Multiset.fold (Multiset V) (· + ·) _ _ ∅
  ((@Fintype.elems E _ : Finset E)
  |>.filter (λ e => v ∈ G.finishAt e)
  |>.val
  |>.map (λ e => (G.flip e).gofrom v))

def outNeighbors [Fintype E] : Multiset V :=
  @Multiset.fold (Multiset V) (· + ·) _ _ ∅
  ((@Fintype.elems E _ : Finset E)
  |>.filter (λ e => v ∈ G.startAt e)
  |>.val
  |>.map (λ e => G.gofrom e v))

abbrev neighbors [Fintype E] : Multiset V := G.outNeighbors v

def inDegree [Fintype E] : ℕ := Multiset.card (G.inNeighbors v)
def outDegree [Fintype E] : ℕ := Multiset.card (G.outNeighbors v)
abbrev degree [Fintype E] : ℕ := G.outDegree v

private def walkAux : V → List (E × V) → Prop
  | _, [] => True
  | u, w :: ws => G.canGo u w.fst w.snd ∧ walkAux w.snd ws

structure Walk where
  start : V
  tail : List (E × V)
  prop : walkAux G start tail

namespace Walk
variable {G : Graph V E} (w : Walk G)

def length : ℕ := w.tail.length

def isSubpath : Walk G → Walk G → Prop := λ w₁ w₂ => w₁.tail.IsInfix w₂.tail



@[simp]
def vertices : List V := w.start :: w.tail.map Prod.snd

@[simp]
def edges : List E := w.tail.map Prod.fst

@[simp]
def finish : V := w.vertices.getLast (by simp)

def ball (n : ℕ) : Set V :=
  {v | ∃ w : Walk G, w.start = u ∧ w.length ≤ n ∧ w.finish = v}

end Walk

class Path {G : Graph V E} (w : Walk G) : Prop :=
  vNodup : w.vertices.Nodup

class Trail {G : Graph V E} (w : Walk G) : Prop :=
  eNodup : w.edges.Nodup

class Closed {G : Graph V E} (w : Walk G) : Prop :=
  startFinish : w.start = w.finish

class Cycle {G : Graph V E} (w : Walk G) extends Closed w : Prop :=
  vNodup' : w.vertices.tail.Nodup

class Tour {G : Graph V E} (w : Walk G) extends Closed w, Trail w: Prop

def Acyclic (G : Graph V E) : Prop := ∀ w : Walk G, ¬ G.Cycle w


def conn (G : Graph V E) (u v : V) : Prop := ∃ w : Walk G, w.start = u ∧ w.finish = v

class connected (G : Graph V E) : Prop :=
  all_conn : ∀ u v : V, conn G u v

def connected_component (G : Graph V E) (v : V) : Set V := {u | G.conn u v}

def cut (G : Graph V E) (S : Finset E) : Prop :=
  ∃ u v, G.conn u v ∧ ∀ w : Walk G, w.start = u ∧ w.finish = v → ∃ e ∈ S, e ∈ w.edges

def bridge (G : Graph V E) (e : E) : Prop := G.cut {e}

def mincut (G : Graph V E) (S : Finset E) : Prop :=
  IsSmallest (G.cut ·) S

class Nconnected (G : Graph V E) (n : ℕ) : Prop :=
  all_conn : ∀ u v : V, conn G u v
  no_small_cut : ∀ S : Finset E, S.card < n → ¬ G.cut S

variable (H : Graph W F)

structure Hom where
  fᵥ : V → W
  fₑ : E → F
  comm : ∀ e, H.inc (fₑ e) = G.map e fᵥ

notation:20 lhs:20 " ⊆ᵍ " rhs:20 => Nonempty (Hom lhs rhs)

structure Isom where
  toHom : Hom G H
  toInv : Hom H G
  left_cancelᵥ : ∀ v, toHom.fᵥ (toInv.fᵥ v) = v
  right_cancelᵥ : ∀ v, toInv.fᵥ (toHom.fᵥ v) = v
  left_cancelₑ : ∀ e, toHom.fₑ (toInv.fₑ e) = e
  right_cancelₑ : ∀ e, toInv.fₑ (toHom.fₑ e) = e

def Hom.inj (a : Hom G H) : Prop := a.fᵥ.Injective ∧ a.fₑ.Injective

def Hom.surj (a : Hom G H) : Prop := a.fᵥ.Surjective ∧ a.fₑ.Surjective


end Graph
