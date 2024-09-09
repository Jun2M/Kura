import Kura.Edges


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
@[simp] abbrev flip : edge V := (G.inc e).flip
@[simp] abbrev map (f : V → W) : edge W := (G.inc e).map f

/-- A full graph is one with no half-edges.-/
class fullGraph : Prop :=
  no_half : ∀ e, G.isFull e

/-- An undirected graph is a full graph with no arcs -/
class undirected extends fullGraph G :=
  edge_symm : ∀ e, G.isUndir e

/-- A loopless graph is one with no loops, free edges or half_edges
  (so every edge is an arc or edge ) -/
class loopless extends fullGraph G :=
  no_loops : ∀ e, ¬G.isLoop e

class multiGraph extends undirected G :=
  no_free : ∀ e, ¬G.isFree e

/-- A simple graph is one where every edge is a actual undirected 'edge'
  and no two edges have the same ends.  -/
class simple extends loopless G, undirected G :=
  inc_inj : G.inc.Injective


def toEdgeMultiset [Fintype E] : Multiset (edge V) :=
  (@Fintype.elems E _ : Finset E)
  |>.val
  |>.map G.inc

unsafe instance [Repr V] [Fintype E] : Repr (Graph V E) where
  reprPrec G _ := "Graph " ++ repr G.toEdgeMultiset



def Complete (V : Type*) [DecidableEq V] : Graph V {u : Sym2 V // ¬ u.IsDiag} where
  inc e := undir e.val
#eval Complete (Fin 5)

def Cycle (n : ℕ+) : Graph (Fin n) (Fin n) where
  inc e := undir s(e, e+1)
#eval Cycle 5

def Path (n : ℕ+) : Graph (Fin n) (Fin (n-1)) where
  inc e := undir s(e, e+1)

def BipComplete (n₁ n₂ : ℕ+) : Graph (Fin n₁ ⊕ Fin n₂) (Fin n₁ × Fin n₂) where
  inc e := undir s(.inl e.1, .inr e.2)
#eval BipComplete 3 4

def adj : Prop := ∃ e, u ∈ (G.inc e).startAt ∧ v ∈ (G.inc e).finishAt

def neighbourhood : Set V := {u | G.adj u v}

def inNeighbors [Fintype E] : Multiset V :=
  @Multiset.fold (Multiset V) (· + ·) _ _ ∅
  ((@Fintype.elems E _ : Finset E)
  |>.filter (λ e => v ∈ (G.inc e).finishAt)
  |>.val
  |>.map (λ e => (G.inc e).flip.gofrom v))

def outNeighbors [Fintype E] : Multiset V :=
  @Multiset.fold (Multiset V) (· + ·) _ _ ∅
  ((@Fintype.elems E _ : Finset E)
  |>.filter (λ e => v ∈ (G.inc e).startAt)
  |>.val
  |>.map (λ e => (G.inc e).gofrom v))

#eval (Complete (Fin 5)).outNeighbors 4

def inDegree [Fintype E] : ℕ := Multiset.card (G.inNeighbors v)
def outDegree [Fintype E] : ℕ := Multiset.card (G.outNeighbors v)

#eval (Complete (Fin 5)).outDegree 3

structure Walk [Inhabited E] where
  start : V
  tail : List (E × V)
  prop : tail.Chain (λ u v => u.snd >>= G.gofrom? v.fst = v.snd) (default, start)

namespace Walk
variable {G : Graph V E} [Inhabited E] (w : Walk G)

def length : ℕ := w.tail.length

def Subpath : Walk G → Walk G → Prop := λ w₁ w₂ => w₁.tail.IsInfix w₂.tail



@[simp]
def vertices : List V := w.start :: w.tail.map Prod.snd

@[simp]
def edges : List E := w.tail.map Prod.fst

@[simp]
def finish : V := w.vertices.getLast (by simp)

def ball (n : ℕ) : Set V :=
  {v | ∃ w : Walk G, w.start = u ∧ w.length ≤ n ∧ w.finish = v}

end Walk

variable (H : Graph W F)

structure Hom where
  fᵥ : V → W
  fₑ : E → F
  comm : ∀ e, H.inc (fₑ e) = (G.inc e).map fᵥ

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
