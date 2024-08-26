import Kura.Edges


-- @[ext]
-- structure GraphN (n m : ENat) where
--   inc : FinE m → edge (FinE n)

-- namespace GraphN
-- open edge
-- variable {n m : ENat} (G : GraphN n m) (e : FinE m) (u v : FinE n)

-- def boundE : Set (FinE m) := {e : FinE m | G.inc e ≠ dir (none, none)}

-- def passible : Bool :=
--   match G.inc e with
--   | undir s => s == s(u, v)
--   | dir (some a, some b) => a = u ∧ b = v
--   | _ => false

-- lemma mem_boundE_iff_ends_nonempty (e : FinE m) : e ∈ G.boundE ↔ (G.inc e).endAt ≠ ∅ := by
--   unfold boundE endAt
--   match hag : G.inc e with
--   | dir (a, b) => cases a <;> cases b <;> simp [hag]
--   | undir s =>
--     simp [ne_eq, Set.mem_setOf_eq, hag, not_false_eq_true, Multiset.empty_eq_zero, true_iff]
--     apply_fun Multiset.card
--     simp

-- lemma isFull_of_isUndir (h : (G.inc e).isUndir) : (G.inc e).isFull := by
--   match hag : G.inc e with
--   | dir _ => simp [hag] at h
--   | undir _ => simp

-- lemma dir_or_undir (e : FinE m) : (G.inc e).isDir ∨ (G.inc e).isUndir := by
--   cases G.inc e <;> simp

-- def edge_between (e : FinE m) (v₁ v₂ : FinE n) : Prop :=
--   G.inc e = undir s(v₁, v₂)

-- /-- Two vertices are adjacent if there is an edge having both vertices as ends. -/
-- def adj (u v : FinE n) : Prop := ∃ e, u ∈ (G.inc e).endAt ∧ v ∈ (G.inc e).endAt

-- /-- A full graph is one with no half-edges. Can have a free edge!-/
-- class FullGraph : Prop :=
--   no_half : ∀ e, ¬ (G.inc e).isHalf

-- /-- An undirected graph is a full graph with no arcs -/
-- class Undirected extends FullGraph G :=
--   edge_symm : ∀ e, (G.inc e).isUndir

-- /-- A loopless graph is one with no loops, free edges or half_edges
--   (so every edge is an arc or edge ) -/
-- class Loopless extends FullGraph G :=
--   no_loops : ∀ e, ¬(G.inc e).isLoop

-- -- class multiGraph extends undirected G :=
-- -- (no_free : ∀ e, ¬G.free e)

-- /-- A simple graph is one where every edge is a actual undirected 'edge'
--   and no two edges have the same ends.  -/
-- class Simple extends Loopless G, Undirected G :=
--   inc_inj : G.inc.Injective

-- -- def edge_set : Set (FinE n × FinE n) := { e | G.edge_between e e.1 e.2 }

-- -- induction!!!! (Finsupp.induction?)

-- end GraphN


@[ext]
structure Graph (V E : Type*) [DecidableEq V] where
  inc : E → edge V

namespace Graph
open edge
variable {V W E F : Type*} [DecidableEq V] [DecidableEq W] (G : Graph V E) (e : E) (u v w : V)


/- Carry the defs from Edges to Graph -/
@[simp] def isDir : Bool := (G.inc e).isDir
@[simp] def isUndir : Bool := (G.inc e).isUndir
@[simp] def isFull : Bool := (G.inc e).isFull
@[simp] def isHalf : Bool := (G.inc e).isHalf
@[simp] def isFree : Bool := (G.inc e).isFree
@[simp] def isLoop : Bool := (G.inc e).isLoop
@[simp] def isArc : Bool := (G.inc e).isArc
@[simp] def endAt : Multiset V := (G.inc e).endAt
@[simp] def startAt : Multiset V := (G.inc e).startAt
@[simp] def finishAt : Multiset V := (G.inc e).finishAt
@[simp] def gofrom (v : V) : Multiset V := (G.inc e).gofrom v
@[simp] def gofrom? (v : V) : Option V := (G.inc e).gofrom? v
@[simp] def goback? (v : V) : Option V := (G.inc e).goback? v
@[simp] def flip : edge V := (G.inc e).flip
@[simp] def map (f : V → W) : edge W := (G.inc e).map f

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



-- -- example graphs
-- @[simp]
-- def CompleteGraphN (n : Nat) : GraphN n (n.choose 2) where
--   inc e := edge.undir <| ⟨((List.FinERange n).sublistsLen 2).get (e.cast (by simp)), by sorry⟩

-- instance : simple (CompleteGraphN n) where
--   no_half := fun e => by simp
--   no_loops := fun e => by
--     simp
--     obtain h := (Sym.listCombinations 2 (List.FinERange n))[e.val].coe_mk_eq.symm
--     rw [h]
--     simp




--   edge_symm := by sorry
--   inc_inj := by sorry

-- -- Path

-- def takeEdge (e : FinE m) (u : V) : Option V := match G.inc e with
--   | dir (some a, b) => if a = u then b else none
--   | undir m =>
--     let m' := (Sym2.equivMultiset V).symm m
--     if h : u ∈ m'
--     then @Sym2.Mem.other' V _ u m' h
--     else none
--   | _ => none

-- lemma takeEdge_eq_some_iff_passible (e : FinE m) (u v : FinE n) : G.takeEdge e u = some v ↔ G.passible e u v = true := by
--   unfold takeEdge passible
--   match G.inc e with
--   | dir (a, b) => cases a <;> cases b <;> simp
--   | undir m =>
--     simp only [decide_eq_true_eq]
--     have hm : m.val = {u, v} ↔ m = ⟨{u, v}, by rfl ⟩ := by
--       convert Subtype.coe_inj
--       rfl
--     rw [hm]; clear hm
--     by_cases h : u ∈ (Sym2.equivMultiset V).symm m
--     · simp only [h, ↓reduceDIte, Option.some.injEq]
--       constructor
--       · -- 1.
--         intro hother
--         apply_fun (Sym2.equivMultiset V).symm
--         rw [Sym2.equivMultisetsymmEq, ← hother, eq_comm]
--         exact Sym2.other_spec' h
--       · -- 2.
--         intro huv
--         subst m
--         simp only [Sym2.equivMultisetsymmEq] at h ⊢
--         exact Sym2.other'_eq_right u v
--     · simp only [h, ↓reduceDIte, false_iff, ne_eq]
--       contrapose! h
--       subst m
--       rw [Sym2.mem_equivMultisetsymm_mem]
--       simp



-- -- Connectedness

-- structure dirPath where
--   start : V
--   tail : List E
--   prop : (tail.foldl (λ (a : Option V) (p : E) => a >>= G.takeEdge p) (some start)).isSome

-- def dirPath.Finish (p : dirPath G) : V :=
--   (p.tail.foldl (λ (a : Option V) (p : E) => a >>= G.takeEdge p) (some p.start)).get p.prop



-- def conn (u v : FinE n) : Prop :=
--   ∃ p : dirPath G, p.start = u ∧ p.tail ≠ [] ∧ (p.tail.last).finish = v
