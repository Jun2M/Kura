import Kura.Graph.Edges
import Kura.Dep.Embedding



@[ext]
structure Graph (V E : Type*) where
  inc : E → edge V

namespace Graph
open edge
variable {U V W E F E' : Type*} (G : Graph V E) (e e' : E) (u v w : V)

def Verts (_G : Graph V E) := V
def Edges (_G : Graph V E) := E

def toEdgeMultiset [Fintype E] : Multiset (edge V) :=
  (@Fintype.elems E _ : Finset E)
  |>.val
  |>.map G.inc

unsafe instance [Repr V] [Fintype E] : Repr (Graph V E) where
  reprPrec G _ := "Graph " ++ repr G.toEdgeMultiset

/- Carry the defs from Edges to Graph -/
@[simp] abbrev isDir : Prop := (G.inc e).isDir
@[simp] abbrev isUndir : Prop := (G.inc e).isUndir
@[simp] abbrev isFull : Prop := (G.inc e).isFull
@[simp] abbrev isHalf : Prop := (G.inc e).isHalf
@[simp] abbrev isFree : Prop := (G.inc e).isFree
@[simp] abbrev isLoop : Prop := (G.inc e).isLoop
@[simp] abbrev isArc : Prop := (G.inc e).isArc
@[simp] abbrev endAt : Multiset V := (G.inc e).endAt
@[simp] abbrev startAt : Multiset V := (G.inc e).startAt
@[simp] abbrev finishAt : Multiset V := (G.inc e).finishAt
@[simp] abbrev gofrom? [DecidableEq V] (v : V) (e : E): Option V := (G.inc e).gofrom? v
@[simp] abbrev goback? [DecidableEq V] (v : V) (e : E) : Option V := (G.inc e).goback? v
@[simp] abbrev canGo [DecidableEq V] (v : V) (e : E) (w : V) : Bool := (G.inc e).canGo v w
@[simp] abbrev flip : edge V := (G.inc e).flip
@[simp] abbrev any := (G.inc e).any
@[simp] abbrev all := (G.inc e).all


/-- A full graph is one with no half-edges.-/
class fullGraph : Prop where
  all_full : ∀ e, G.isFull e

/-- An undirected graph is a full graph with no arcs -/
class Undirected extends fullGraph G : Prop where
  edge_symm : ∀ e, G.isUndir e

/-- A loopless graph is one with no loops, free edges or half_edges
  (so every edge is an arc or edge ) -/
class loopless extends fullGraph G : Prop where
  no_loops : ∀ e, ¬G.isLoop e


/-- A simple graph is one where every edge is a actual undirected 'edge'
  and no two edges have the same ends.  -/
class Simple extends loopless G, Undirected G : Prop where
  inc_inj : G.inc.Injective

class Directed extends fullGraph G : Prop where
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
def incEE [DecidableEq V] := λ e => {e' | (e = e' ∧ G.isLoop e) ∨ (e ≠ e' ∧ G.startAt e ∩ G.finishAt e' ≠ ∅)}

lemma loop_mem_incEE [DecidableEq V] (hloop : G.isLoop e) : e ∈ G.incEE e := by
  simp only [incEE, Set.mem_setOf_eq, true_and]
  exact Or.inl hloop

lemma ne_of_mem_incEE_of_notLoop [DecidableEq V] (h : e' ∈ G.incEE e) (hloop : ¬G.isLoop e) :
    e ≠ e' := by
  rintro rfl
  simp only [incEE, isLoop, ne_eq, startAt, finishAt, Multiset.empty_eq_zero, Set.mem_setOf_eq,
    true_and, not_true_eq_false, false_and, or_false] at h
  exact hloop h

def adj [DecidableEq V] (u v : V) : Prop := ∃ e, G.canGo u e v
def neighbourhood [DecidableEq V] : Set V := {u | G.adj u v}

macro u:term "—[" e:term "]—" v:term : term => `(G.canGo $u $e $v)

instance instAdjDecidable {G : Graph V E} [DecidableEq V] [Fintype E] (v : V) :
    DecidablePred (G.adj v) := by
  rintro w
  simp only [adj, canGo, edge.canGo, Option.mem_def, decide_eq_true_eq]
  infer_instance

lemma adj_eq_bot_of_IsEmpty_E [DecidableEq V] [IsEmpty E] : G.adj = ⊥ := by
  ext u v
  simp only [adj, canGo, IsEmpty.exists_iff, Pi.bot_apply, «Prop».bot_eq_false]

variable {G : Graph V E} {H : Graph W F} {I : Graph U E'} {J : Graph V' F'} [DecidableEq V]
  [DecidableEq W] [DecidableEq U] [DecidableEq V']

-- Disjoint union of two graphs
def add : Graph (V ⊕ W) (E ⊕ F) where
  inc e := match e with
    | Sum.inl e₁ => (G.inc e₁).map Sum.inl
    | Sum.inr e₂ => (H.inc e₂).map Sum.inr

/-- A homomorphism between graphs `G = (V,E)` and `H = (W,F)` is a map between
    vertex sets that preserves adjacency. It is implemented as two functions,
    `fᵥ : V → W` and `fₑ : E → F` such that for all `(u,v) ∈ E, fₑ (u,v) = (fᵥ(u),fᵥ(v))`.-/
structure Hom (G : Graph V E) (H : Graph W F) where
  fᵥ : V → W
  fₑ : E → F
  inc : ∀ e, H.inc (fₑ e) = (G.inc e).map fᵥ

namespace Hom

omit [DecidableEq V] [DecidableEq W] in @[ext]
lemma ext (A B : Hom G H) (h : A.fᵥ = B.fᵥ) (h' : A.fₑ = B.fₑ) : A = B := by
  cases A; cases B
  congr

def refl (G : Graph V E) : Hom G G := ⟨id, id, fun _ => by rw [id_eq, map_id]⟩

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma refl_fᵥ : (Hom.refl G).fᵥ = id := rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma refl_fₑ : (Hom.refl G).fₑ = id := rfl

/-- From two homomorphisms `Hom G H` and `Hom H I`, we can compose them to obtain
    a `Hom G I`.-/
def trans (A : Hom G H) (B : Hom H I) : Hom G I where
  fᵥ := B.fᵥ ∘ A.fᵥ
  fₑ := B.fₑ ∘ A.fₑ
  inc e := by simp only [Function.comp_apply, B.inc, A.inc, map_comp]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma trans_fᵥ (A : Hom G H) (B : Hom H I) : (A.trans B).fᵥ = B.fᵥ ∘ A.fᵥ := rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma trans_fₑ (A : Hom G H) (B : Hom H I) : (A.trans B).fₑ = B.fₑ ∘ A.fₑ := rfl

def add (A : Hom G H) (B : Hom H J) : Hom 

def union (A : Hom G I) (B : Hom H I) : Graph (V ⊕ W) (E ⊕ F) where
  inc := λ e => match e with
    | inl e => A.fₑ e
    | inr e => B.fₑ e

lemma canGo (A : Hom G H) {u v : V} {e : E} (h : G.canGo u e v):
    H.canGo (A.fᵥ u) (A.fₑ e) (A.fᵥ v) := by
  simp only [Graph.canGo, A.inc e]
  rwa [map_canGo]

lemma adj (A : Hom G H) {u v : V} (h : G.adj u v) : H.adj (A.fᵥ u) (A.fᵥ v) := by
  obtain ⟨e, he⟩ := h
  exact ⟨A.fₑ e, A.canGo he⟩

lemma adj_le (A : Hom G H) : Relation.Map G.adj A.fᵥ A.fᵥ ≤ H.adj := by
  rintro u v ⟨x, y, hxy, rfl, rfl⟩
  exact A.adj hxy

end Hom

/-- `G` is a subgraph of `H`, written `G ⊆ᴳ H`, if there exists a `Hom G H` where the
    map between the vertices and the edges are `Injective`.-/
structure SubgraphOf (G : Graph V E) (H : Graph W F) extends Hom G H where
  fᵥinj : fᵥ.Injective
  fₑinj : fₑ.Injective

macro G:term "⊆ᴳ" H:term :term => `(Graph.SubgraphOf $G $H)

-- unsafe instance [Repr W] [Repr V] [Fintype E] [Fintype F] : Repr (G ⊆ᴳ H) where
--   reprPrec _SubgraphOf _ := repr G ++ " ⊆ᴳ " ++ repr H

namespace SubgraphOf

omit [DecidableEq V] [DecidableEq W] in @[ext]
lemma ext (A B : G ⊆ᴳ H) (h : A.fᵥ = B.fᵥ) (h' : A.fₑ = B.fₑ) : A = B := by
  cases A; cases B
  congr
  ext <;> simp_all only

def refl (G : Graph V E) : G ⊆ᴳ G where
  toHom := Hom.refl G
  fᵥinj _ _ h := h
  fₑinj _ _ h := h

variable (A : G ⊆ᴳ H)

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma refl_fᵥ : (SubgraphOf.refl G).fᵥ = id := rfl
omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma refl_fₑ : (SubgraphOf.refl G).fₑ = id := rfl

def fᵥEmb : V ↪ W := ⟨A.fᵥ, A.fᵥinj⟩
def fₑEmb : E ↪ F := ⟨A.fₑ, A.fₑinj⟩

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma fᵥEmb_apply : A.fᵥEmb v = A.fᵥ v := rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma fₑEmb_apply : A.fₑEmb e = A.fₑ e := rfl

def trans (B : H ⊆ᴳ I) : G ⊆ᴳ I where
  toHom := A.toHom.trans B.toHom
  fᵥinj := (A.fᵥEmb.trans B.fᵥEmb).inj'
  fₑinj _ _ h := (A.fₑEmb.trans B.fₑEmb).inj' h

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma trans_fᵥ (A : G ⊆ᴳ H) (B : H ⊆ᴳ I) : (A.trans B).fᵥ = B.fᵥ ∘ A.fᵥ := rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma trans_fₑ (A : G ⊆ᴳ H) (B : H ⊆ᴳ I) : (A.trans B).fₑ = B.fₑ ∘ A.fₑ := rfl

/-- Let `G ⊆ᴳ H`, we can travel from `u` to `v` via edge `e` in `G`
    iff we can travel from `fᵥ(u)` to `fᵥ(v)` via edge `fₑ(e)` in `H`.-/
lemma canGo_iff (u : V) (e : E) (v : V) :
    H.canGo (A.fᵥ u) (A.fₑ e) (A.fᵥ v) ↔ G.canGo u e v := by
  refine ⟨?_, A.toHom.canGo⟩
  rintro h
  match h' : H.inc (A.fₑ e) with
  | dir d =>
    simp only [canGo, h', canGo_iff_eq_of_dir] at h
    subst h
    simp only [A.inc e, map_eq_dir, Option.map_eq_some'] at h'
    obtain ⟨_, _, hinc, ⟨x, rfl, hx⟩, ⟨y, rfl, hy⟩⟩ := h'
    rw [A.fᵥinj hx, A.fᵥinj hy] at hinc
    simp only [canGo, hinc, dir_canGo]
  | undir s =>
    simp only [canGo, h', canGo_iff_eq_of_undir] at h
    subst h
    simp only [A.inc e, map_eq_undir] at h'
    obtain ⟨s, hs, h'⟩ := h'
    rw [Sym2.map_eq_iff A.fᵥinj] at h'
    subst h'
    unfold canGo
    simp only [hs, canGo_iff_eq_of_undir]

noncomputable def FintypeV [Fintype W] (A : G ⊆ᴳ H) : Fintype V := by
  exact Fintype.ofInjective A.fᵥ A.fᵥinj

noncomputable def FintypeE [Fintype F] (A : G ⊆ᴳ H) : Fintype E := by
  exact Fintype.ofInjective A.fₑ A.fₑinj

end SubgraphOf

/-- A subgraph `G ⊆ᴳ H` is spanning if `V(G)=V(H)` i.e. `fᵥ` is surjective.-/
structure SpanningSubgraphOf (G : Graph V E) (H : Graph W F) extends G ⊆ᴳ H where
  fᵥsurj : fᵥ.Surjective

namespace SpanningSubgraphOf
variable (A : G.SpanningSubgraphOf H)

omit [DecidableEq V] [DecidableEq W] in @[ext]
lemma ext (A B : G.SpanningSubgraphOf H) (h : A.fᵥ = B.fᵥ) (h' : A.fₑ = B.fₑ) : A = B := by
  cases A; cases B
  congr
  ext <;> simp_all only

def fᵥBij : Function.Bijective A.fᵥ where
  left := A.fᵥinj
  right := A.fᵥsurj

noncomputable abbrev fᵥEquiv : V ≃ W := Equiv.ofBijective _ A.fᵥBij

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma fᵥEquiv_apply : A.fᵥEquiv = A.fᵥ := by
  ext v
  rfl

end SpanningSubgraphOf

structure QuotientGraphOf (G : Graph V E) (H : Graph W F) extends G ⊆ᴳ H where
  fₑsurj : fₑ.Surjective

namespace QuotientGraphOf

end QuotientGraphOf

/-- The graphs `G=(V,E)` and `H=(W,F)` are isomorphic, denoted `G ≃ᴳ H` if there is a homomorphism
    `Hom G H` such that `fᵥ : V → W` and `fₑ : E → F` are both `Injective` and `Surjective`. -/
structure Isom (G : Graph V E) (H : Graph W F) extends SpanningSubgraphOf G H where
  fₑsurj : fₑ.Surjective

macro G:term "≃ᴳ" H:term :term => `(Graph.Isom $G $H)

namespace Isom

variable (A : G ≃ᴳ H)

omit [DecidableEq V] [DecidableEq W] in @[ext]
lemma ext (A B : G ≃ᴳ H) (h : A.fᵥ = B.fᵥ) (h' : A.fₑ = B.fₑ) : A = B := by
  cases A; cases B
  congr
  ext <;> simp_all only

def fₑBij : Function.Bijective A.fₑ where
  left := A.fₑinj
  right := A.fₑsurj

noncomputable abbrev fₑEquiv : E ≃ F := Equiv.ofBijective _ A.fₑBij

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma fᵥEquiv_apply : A.fᵥEquiv v = A.fᵥ v := rfl

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma fₑEquiv_apply : A.fₑEquiv e = A.fₑ e := rfl

lemma Equiv.ofBijective_symm_comp {α β : Sort*} (f : α → β) (hf : Function.Bijective f) :
  (Equiv.ofBijective f hf).symm ∘ f = id :=
    (Equiv.symm_comp_eq (Equiv.ofBijective f hf) id f).mpr rfl

def OfEquivs (Efᵥ : V ≃ W) (Efₑ : E ≃ F) (hinc : ∀ e, H.inc (Efₑ e) = (G.inc e).map Efᵥ) :
    G ≃ᴳ H where
  fᵥ := Efᵥ
  fₑ := Efₑ
  inc := hinc
  fᵥinj := Equiv.injective Efᵥ
  fᵥsurj := Equiv.surjective Efᵥ
  fₑinj := Equiv.injective Efₑ
  fₑsurj := Equiv.surjective Efₑ

def refl (G : Graph V E) : G ≃ᴳ G where
  toSubgraphOf := SubgraphOf.refl G
  fᵥsurj := fun x => exists_apply_eq_apply (SubgraphOf.refl G).fᵥ x
  fₑsurj := fun x => exists_apply_eq_apply (SubgraphOf.refl G).fₑ x

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma refl_fᵥ : (Isom.refl G).fᵥ = Equiv.refl _ := rfl

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma refl_fₑ : (Isom.refl G).fₑ = Equiv.refl _ := rfl

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma refl_fᵥEquiv : (Isom.refl G).fᵥEquiv = Equiv.refl _ := by
  ext v
  rfl

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma refl_fₑEquiv : (Isom.refl G).fₑEquiv = Equiv.refl _ := by
  ext e
  rfl

noncomputable def symm : H ≃ᴳ G := OfEquivs A.fᵥEquiv.symm A.fₑEquiv.symm (by
  intro e
  have := A.inc (A.fₑEquiv.symm e)
  rw [Equiv.ofBijective_apply_symm_apply _ A.fₑBij] at this
  rw [this, ← map_comp, Equiv.ofBijective_symm_comp _ A.fᵥBij, map_id])

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma symm_fᵥ : A.symm.fᵥ = A.fᵥEquiv.symm := rfl

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma symm_fₑ : A.symm.fₑ = A.fₑEquiv.symm := rfl

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma symm_fᵥEquiv : A.symm.fᵥEquiv = A.fᵥEquiv.symm := by
  ext v
  rfl

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma symm_fₑEquiv : A.symm.fₑEquiv = A.fₑEquiv.symm := by
  ext e
  rfl

def trans (B : H ≃ᴳ I) : G ≃ᴳ I where
  toSubgraphOf := A.toSubgraphOf.trans B.toSubgraphOf
  fᵥsurj := B.fᵥsurj.comp A.fᵥsurj
  fₑsurj := B.fₑsurj.comp A.fₑsurj

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma trans_fᵥ (B : H ≃ᴳ I) : (A.trans B).fᵥ = B.fᵥ ∘ A.fᵥ := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma trans_fₑ (B : H ≃ᴳ I) : (A.trans B).fₑ = B.fₑ ∘ A.fₑ := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma trans_fᵥEquiv (B : H ≃ᴳ I) : (A.trans B).fᵥEquiv = A.fᵥEquiv.trans B.fᵥEquiv := by
  ext v
  rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma trans_fₑEquiv (B : H ≃ᴳ I) : (A.trans B).fₑEquiv = A.fₑEquiv.trans B.fₑEquiv := by
  ext e
  rfl

lemma canGo_iff (u : V) (e : E) (v : V) :
    H.canGo (A.fᵥ u) (A.fₑ e) (A.fᵥ v) ↔ G.canGo u e v := SubgraphOf.canGo_iff A.toSubgraphOf u e v

lemma adj_iff (u v : V) : H.adj (A.fᵥ u) (A.fᵥ v) ↔ G.adj u v := by
  refine ⟨?_, A.toSubgraphOf.adj⟩
  rintro h
  convert A.symm.toSubgraphOf.adj h <;> simp only [symm_fᵥ, Equiv.ofBijective_symm_apply_apply]

end Isom

def Aut (G : Graph V E) := G ≃ᴳ G

namespace Aut

noncomputable instance instAutGroup : Group G.Aut where
  mul A B := A.trans B
  mul_assoc A B C := by
    change (A.trans B).trans C = A.trans (B.trans C)
    ext <;> simp [Isom.trans_fᵥ, Function.comp_apply]
  one := Isom.refl G
  one_mul A := by
    change (Isom.refl G).trans A = A
    ext <;> simp [Isom.trans_fᵥ, Isom.refl_fᵥ, Equiv.coe_refl, Function.comp_apply, id_eq]
  mul_one A := by
    change A.trans (Isom.refl G) = A
    ext <;> simp
  inv A := A.symm
  inv_mul_cancel A := by
    change A.symm.trans A = Isom.refl G
    ext <;> simp
    rw [← Isom.fᵥEquiv_apply, Equiv.apply_symm_apply]
    rw [← Isom.fₑEquiv_apply, Equiv.apply_symm_apply]

end Aut


end Graph
