import Kura.Graph.Edges
import Kura.Dep.Finset


@[ext]
structure Graph (V E : Type*) [LinearOrder V] where
  inc : E → edge V

namespace Graph
open edge
variable {V W E F : Type*} [LinearOrder V] [LinearOrder W] (G : Graph V E) (e : E) (u v w : V)


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
class Simple extends loopless G, Undirected G :=
  inc_inj : G.inc.Injective

class Directed extends fullGraph G :=
  no_undir : ∀ e, ¬G.isUndir e

class Searchable :=
  outEdges : V → Finset E
  outEdges_mem : ∀ v e, e ∈ outEdges v ↔ v ∈ G.inc e

def outEdges [Searchable G] (v : V) : Finset E := Searchable.outEdges G v

lemma mem_outEdges [Searchable G] : e ∈ G.outEdges v ↔ v ∈ G.inc e := by
  rw [← Searchable.outEdges_mem (G := G) v e]
  rfl

instance Searchable_of_FintypeE [Fintype E] : Searchable G where
  outEdges v := Fintype.elems.filter (λ e => v ∈ G.inc e)
  outEdges_mem v e := by
    rw [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun _ => Fintype.complete e

lemma exist_Sym2 [Undirected G] : ∃ s, G.inc e = undir s := by
  match h : G.inc e with
  | dir (a, b) =>
    have := @Undirected.edge_symm _ _ _ G _ e
    cases a <;> cases b <;> simp_all
  | undir s => exact ⟨s, rfl⟩

@[simp]
lemma not_dir_none_none [fullGraph G] : G.inc e ≠ dir (none, none) := by
  intro h
  have := fullGraph.all_full (G := G) e
  simp only [isFull, edge.isFull, h, Bool.false_eq_true] at this


@[simp]
lemma not_dir_some_none [fullGraph G] : G.inc e ≠ dir (some u, none) := by
  intro h
  have := fullGraph.all_full (G := G) e
  simp only [isFull, edge.isFull, h, Bool.false_eq_true] at this

@[simp]
lemma not_dir_none_some [fullGraph G] : G.inc e ≠ dir (none, some u) := by
  intro h
  have := fullGraph.all_full (G := G) e
  simp only [isFull, edge.isFull, h, Bool.false_eq_true] at this

@[simp]
lemma endAt_card_two [fullGraph G] : Multiset.card (G.endAt e) = 2 := by
  match h : G.inc e with
  | dir (a, b) => cases a <;> cases b <;> simp_all
  | undir s => simp only [endAt, edge.endAt, h, Sym2.toMultiset_card]


lemma exist_two_mem [fullGraph G] : ∃ u v, u ∈ G.inc e ∧ v ∈ G.inc e := by
  obtain ⟨u, v, h⟩ := Multiset.card_eq_two.mp (endAt_card_two G e)
  refine ⟨u, v, ?_, ?_⟩ <;> simp only [instedgeMem, h, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton, true_or, or_true]

@[simp]
lemma gofrom?_isSome_iff_mem_startAt [fullGraph G] (v : V) (e : E) :
    (G.gofrom? v e).isSome ↔ v ∈ G.startAt e := by
  simp [startAt, edge.startAt, gofrom?, edge.gofrom?]
  match he : G.inc e with
  | dir (a, b) => cases a <;> cases b <;> simp_all ; rw [Eq.comm]
  | undir s => simp only [Option.isSome_dite, Sym2.mem_toMultiset_iff]


def get [Undirected G] : Sym2 V :=
  match h : G.inc e with
  | dir (a, b) => by
    have := Undirected.edge_symm (G := G) e
    rw [isUndir, h] at this
    exact (not_isUndir_of_dir _ _ this).elim
  | undir s => s

@[simp]
lemma mem_get_iff_mem_inc [Undirected G] : v ∈ G.get e ↔ v ∈ G.inc e := by
  match h : G.inc e with
  | dir (a, b) =>
    have := @Undirected.edge_symm _ _ _ G _ e
    cases a <;> cases b <;> simp_all only [isUndir, not_isUndir_of_dir, Bool.false_eq_true]
  | undir s =>
    simp [get, h]
    split <;> simp_all

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

lemma get_inf_mem_inc [Undirected G] : (G.get e).inf ∈ G.inc e := by
  simp only [instedgeMem, edge.endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
    List.foldl_cons, Multiset.cons_zero, List.foldl_nil, inc_eq_undir_get, Sym2.mem_toMultiset_iff,
    Sym2.inf_mem]

lemma get_sup_mem_inc [Undirected G] : (G.get e).sup ∈ G.inc e := by
  simp only [instedgeMem, edge.endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
    List.foldl_cons, Multiset.cons_zero, List.foldl_nil, inc_eq_undir_get, Sym2.mem_toMultiset_iff,
    Sym2.sup_mem]

lemma mem_outEdges_iff_mem_get [Searchable G] [Undirected G] : e ∈ G.outEdges v ↔ v ∈ G.get e := by
  rw [mem_outEdges, inc_eq_undir_get]
  simp only [mem_outEdges, instedgeMem, edge.endAt, Multiset.insert_eq_cons, Multiset.empty_eq_zero,
    List.foldl_cons, Multiset.cons_zero, List.foldl_nil, inc_eq_undir_get, mem_undir_iff]

def adj : Prop := ∃ e, G.canGo u e v
def neighbourhood : Set V := {u | G.adj u v}

macro u:term "--" e:term "--" v:term : term => `(G.canGo $u $e $v)

def goFrom [Undirected G] {v : V} {e : E} (h : v ∈ G.get e) : V := Sym2.Mem.other' h

def outNeighbors [Searchable G] : Multiset V :=
  Multiset.eraseNone (G.outEdges v |>.val |>.map (G.gofrom? v ·))

def inNeighbors [Searchable G] : Multiset V :=
  Multiset.eraseNone (G.outEdges v |>.val |>.map (G.goback? v ·))

abbrev neighbors [Searchable G] : Multiset V := G.outNeighbors v

def inDegree [Searchable G] : ℕ := Multiset.card (G.inNeighbors v)
def outDegree [Searchable G] : ℕ := Multiset.card (G.outNeighbors v)
abbrev degree [Searchable G] : ℕ := G.outDegree v
def regular (G : Graph V E) [Searchable G] (k : ℕ) : Prop := ∀ v : V, G.degree v = k

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
