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
class Undirected extends fullGraph G :=
  edge_symm : ∀ e, G.isUndir e

/-- A loopless graph is one with no loops, free edges or half_edges
  (so every edge is an arc or edge ) -/
class loopless extends fullGraph G :=
  no_loops : ∀ e, ¬G.isLoop e

/-- A simple graph is one where every edge is a actual undirected 'edge'
  and no two edges have the same ends.  -/
class simple extends loopless G, Undirected G :=
  inc_inj : G.inc.Injective


lemma exist_Sym2 [Undirected G] : ∃ s, G.inc e = undir s := by
  match h : G.inc e with
  | dir (a, b) =>
    have := @Undirected.edge_symm _ _ _ G _ e
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

lemma exist_mem [fullGraph G] : ∃ v, v ∈ G.inc e := Multiset.exists_mem_of_ne_zero (endAt_ne_zero G e)

def get [Undirected G] : Sym2 V :=
  match h : G.inc e with
  | dir (a, b) => by
    exfalso
    have := @Undirected.edge_symm _ _ _ G _ e
    simp [h] at this
  | undir s => s

@[simp low]
lemma inc_eq_undir_get [Undirected G] : G.inc e = undir (G.get e) := by
  match h : G.inc e with
  | dir (a, b) =>
    have := @Undirected.edge_symm _ _ _ G _ e
    cases a <;> cases b <;> simp_all
  | undir s =>
    simp only [get, h]
    split <;> simp_all

lemma canGo_symm [Undirected G] : G.canGo u e v = G.canGo v e u := by
  simp only [canGo, inc_eq_undir_get]
  rw [← canGo_flip, flip_self]

lemma get_inf_mem_inc (G : Graph V E) [Undirected G] [LinearOrder V] : (G.get e).inf ∈ G.inc e := by
  simp only [instedgeMem, edge.endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
    List.foldl_cons, Multiset.cons_zero, List.foldl_nil, inc_eq_undir_get, Sym2.mem_toMultiset_iff,
    Sym2.inf_mem]

lemma get_sup_mem_inc (G : Graph V E) [Undirected G] [LinearOrder V] : (G.get e).sup ∈ G.inc e := by
  simp only [instedgeMem, edge.endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
    List.foldl_cons, Multiset.cons_zero, List.foldl_nil, inc_eq_undir_get, Sym2.mem_toMultiset_iff,
    Sym2.sup_mem]

def adj : Prop := ∃ e, G.canGo u e v

def neighbourhood : Set V := {u | G.adj u v}

def entrance : Set E := {e | u ∈ G.finishAt e}
def exit : Set E := {e | u ∈ G.startAt e}

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

def regular [Fintype E] (G : Graph V E) (k : ℕ) : Prop := ∀ v : V, G.degree v = k

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
