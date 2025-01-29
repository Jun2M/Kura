import Kura.Graph.Edges
import Kura.Dep.Embedding



@[ext]
structure Graph (V E : Type*) where
  inc : E → edge V

namespace Graph
open edge
variable {U V W E F E' : Type*} (G : Graph V E) (e e' : E) (u v w : V)


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


lemma canGo_eq [DecidableEq V] (e : E) {u v w y : V} (h : G.canGo u e v) (h' : G.canGo w e y) :
    u = w ∧ v = y ∨ u = y ∧ v = w := by
  simp only [canGo] at h h'
  match hinc : G.inc e with
  | dir p =>
    simp only [hinc, canGo_iff_eq_of_dir] at h h'
    subst p
    left
    simpa only [Prod.mk.injEq, Option.some.injEq] using h'
  | undir s =>
    simp only [hinc, canGo_iff_eq_of_undir] at h h'
    subst s
    simpa [Prod.mk.injEq, Option.some.injEq] using h'

/- Basic functions -/
-- def split : Multiset (Option V × E × Option V) := match G.inc e with
--   | dir p => {(p.fst, e, p.snd)}
--   | undir s => {(some s.inf, e, some s.sup), (some s.sup, e, some s.inf)}

def incEV := λ e => {v | v ∈ G.inc e}
def incEsV (E : Set E) : Set V := {v | ∃ e ∈ E, v ∈ G.inc e}
def incVE := λ v => {e | v ∈ G.startAt e}
def incVV := λ v => {u | ∃ e, u ≠ v ∧ u ∈ G.inc e ∧ v ∈ G.inc e}
def incEE [DecidableEq V] := λ e => {e' | (e = e' ∧ G.isLoop e) ∨ (e ≠ e' ∧ G.startAt e ∩ G.finishAt e' ≠ ∅)}

lemma incEsV_union (A B : Set E) : G.incEsV (A ∪ B) = G.incEsV A ∪ G.incEsV B := by
  ext v
  simp only [incEsV, Set.mem_union, Set.mem_setOf_eq, ← exists_or, ← or_and_right]

lemma incEsV_spec (S : Set E) : ∀ e ∈ S, ∀ v ∈ G.inc e, v ∈ G.incEsV S := by
  rintro e he v hve
  simp only [incEsV, Set.mem_setOf_eq]
  use e, he

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
def add (G : Graph V E) (H : Graph W F) : Graph (V ⊕ W) (E ⊕ F) where
  inc e := match e with
    | Sum.inl e₁ => (G.inc e₁).map Sum.inl
    | Sum.inr e₂ => (H.inc e₂).map Sum.inr

instance instHAddGraph : HAdd (Graph V E) (Graph W F) (Graph (V ⊕ W) (E ⊕ F)) where
  hAdd G H := G.add H

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma add_inc : (G + H).inc = λ e => match e with
  | Sum.inl e₁ => (G.inc e₁).map Sum.inl
  | Sum.inr e₂ => (H.inc e₂).map Sum.inr := rfl


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

def add (A : Hom G I) (B : Hom H I) : Hom (G + H) I where
  fᵥ v := match v with
    | Sum.inl v => A.fᵥ v
    | Sum.inr v => B.fᵥ v
  fₑ e := match e with
    | Sum.inl e => A.fₑ e
    | Sum.inr e => B.fₑ e
  inc e := by
    match e with
    | Sum.inl e =>
      rw [add_inc, A.inc, ← edge.map_comp]
      congr
    | Sum.inr e =>
      rw [add_inc, B.inc, ← edge.map_comp]
      congr

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in
lemma add_fᵥ (A : Hom G I) (B : Hom H I) : (A.add B).fᵥ = fun v => match v with
    | Sum.inl v => A.fᵥ v
    | Sum.inr v => B.fᵥ v := rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in
lemma add_fₑ (A : Hom G I) (B : Hom H I) : (A.add B).fₑ = fun e => match e with
    | Sum.inl e => A.fₑ e
    | Sum.inr e => B.fₑ e := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma add_fᵥ_inl (A : Hom G I) (B : Hom H I) : (A.add B).fᵥ ∘ Sum.inl = A.fᵥ := rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma add_fᵥ_inr (A : Hom G I) (B : Hom H I) : (A.add B).fᵥ ∘ Sum.inr = B.fᵥ := rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma add_fₑ_inl (A : Hom G I) (B : Hom H I) : (A.add B).fₑ ∘ Sum.inl = A.fₑ := rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma add_fₑ_inr (A : Hom G I) (B : Hom H I) : (A.add B).fₑ ∘ Sum.inr = B.fₑ := rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma add_fᵥ_inl_apply (A : Hom G I) (B : Hom H I) (v : V) : (A.add B).fᵥ (Sum.inl v) = A.fᵥ v :=
  rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma add_fᵥ_inr_apply (A : Hom G I) (B : Hom H I) (v : W) : (A.add B).fᵥ (Sum.inr v) = B.fᵥ v :=
  rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma add_fₑ_inl_apply (A : Hom G I) (B : Hom H I) (e : E) : (A.add B).fₑ (Sum.inl e) = A.fₑ e :=
  rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma add_fₑ_inr_apply (A : Hom G I) (B : Hom H I) (e : F) : (A.add B).fₑ (Sum.inr e) = B.fₑ e :=
  rfl

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

omit [DecidableEq V] [DecidableEq W] in
lemma isloop (A : Hom G H) {e : E} (he : G.isLoop e) : H.isLoop (A.fₑ e) := by
  simp only [isLoop, A.inc] at he ⊢
  exact map_isLoop A.fᵥ he

end Hom

/-- `G` is a subgraph of `H`, written `G ⊆ᴳ H`, if there exists a `Hom G H` where the
    map between the vertices and the edges are `Injective`.-/
structure Emb (G : Graph V E) (H : Graph W F) extends Hom G H where
  fᵥinj : fᵥ.Injective
  fₑinj : fₑ.Injective

macro G:term "⊆ᴳ" H:term :term => `(Graph.Emb $G $H)

-- unsafe instance [Repr W] [Repr V] [Fintype E] [Fintype F] : Repr (G ⊆ᴳ H) where
--   reprPrec _Emb _ := repr G ++ " ⊆ᴳ " ++ repr H

namespace Emb

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
lemma refl_fᵥ : (Emb.refl G).fᵥ = id := rfl
omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma refl_fₑ : (Emb.refl G).fₑ = id := rfl

def fᵥEmb : V ↪ W := ⟨A.fᵥ, A.fᵥinj⟩
def fₑEmb : E ↪ F := ⟨A.fₑ, A.fₑinj⟩

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma fᵥEmb_apply : A.fᵥEmb v = A.fᵥ v := rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma fₑEmb_apply : A.fₑEmb e = A.fₑ e := rfl

def OfEmbs (fᵥ : V ↪ W) (fₑ : E ↪ F) (hinc : ∀ e, H.inc (fₑ e) = (G.inc e).map fᵥ) : G ⊆ᴳ H where
  fᵥ := fᵥ.toFun
  fₑ := fₑ.toFun
  inc := hinc
  fᵥinj := fᵥ.inj'
  fₑinj := fₑ.inj'

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma OfEmbs_fᵥ : (OfEmbs fᵥ fₑ hinc).fᵥ = fᵥ.toFun := rfl
omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma OfEmbs_fₑ : (OfEmbs fᵥ fₑ hinc).fₑ = fₑ.toFun := rfl

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

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma isLoop_iff {e : E} : H.isLoop (A.fₑ e) ↔ G.isLoop e := by
  simp only [isLoop, A.inc]
  exact map_isLoop_iff A.fᵥEmb

noncomputable def FintypeV [Fintype W] (A : G ⊆ᴳ H) : Fintype V := by
  exact Fintype.ofInjective A.fᵥ A.fᵥinj

noncomputable def FintypeE [Fintype F] (A : G ⊆ᴳ H) : Fintype E := by
  exact Fintype.ofInjective A.fₑ A.fₑinj

end Emb

/-- A subgraph `G ⊆ᴳ H` is spanning if `V(G)=V(H)` i.e. `fᵥ` is surjective.-/
structure SpanningEmb (G : Graph V E) (H : Graph W F) extends G ⊆ᴳ H where
  fᵥsurj : fᵥ.Surjective

namespace SpanningEmb
variable (A : G.SpanningEmb H)

omit [DecidableEq V] [DecidableEq W] in @[ext]
lemma ext (A B : G.SpanningEmb H) (h : A.fᵥ = B.fᵥ) (h' : A.fₑ = B.fₑ) : A = B := by
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

end SpanningEmb

structure QuotientGraphOf (G : Graph V E) (H : Graph W F) extends G ⊆ᴳ H where
  fₑsurj : fₑ.Surjective

namespace QuotientGraphOf

end QuotientGraphOf

/-- The graphs `G=(V,E)` and `H=(W,F)` are isomorphic, denoted `G ≃ᴳ H` if there is a homomorphism
    `Hom G H` such that `fᵥ : V → W` and `fₑ : E → F` are both `Injective` and `Surjective`. -/
structure Isom (G : Graph V E) (H : Graph W F) extends SpanningEmb G H where
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
  toEmb := Emb.refl G
  fᵥsurj := fun x => exists_apply_eq_apply (Emb.refl G).fᵥ x
  fₑsurj := fun x => exists_apply_eq_apply (Emb.refl G).fₑ x

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

omit [DecidableEq V] [DecidableEq W] in
lemma symm_fᵥ : A.symm.fᵥ = A.fᵥEquiv.symm := rfl

omit [DecidableEq V] [DecidableEq W] in
lemma symm_fₑ : A.symm.fₑ = A.fₑEquiv.symm := rfl

omit [DecidableEq V] [DecidableEq W] in
lemma symm_fᵥEquiv : A.symm.fᵥEquiv = A.fᵥEquiv.symm := by
  ext v
  rfl

omit [DecidableEq V] [DecidableEq W] in
lemma symm_fₑEquiv : A.symm.fₑEquiv = A.fₑEquiv.symm := by
  ext e
  rfl

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma symm_fᵥ_fᵥ : A.symm.fᵥ (A.fᵥ v) = v := by
  simp only [symm_fᵥ, Equiv.ofBijective_symm_apply_apply]

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma fᵥ_symm_fᵥ {w : W} : A.fᵥ (A.symm.fᵥ w) = w := by
  simp only [symm_fᵥ, Equiv.ofBijective_apply_symm_apply]

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma symm_fᵥ_comp_fᵥ : A.symm.fᵥ ∘ A.fᵥ = id := by
  ext v
  simp only [Function.comp_apply, symm_fᵥ_fᵥ, id_eq]

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma fᵥ_comp_symm_fᵥ : A.fᵥ ∘ A.symm.fᵥ = id := by
  ext w
  simp only [Function.comp_apply, fᵥ_symm_fᵥ, id_eq]

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma symm_fₑ_fₑ : A.symm.fₑ (A.fₑ e) = e := by
  simp only [symm_fₑ, Equiv.ofBijective_symm_apply_apply]

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma fₑ_symm_fₑ {f : F} : A.fₑ (A.symm.fₑ f) = f := by
  simp only [symm_fₑ, Equiv.ofBijective_apply_symm_apply]

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma symm_fₑ_comp_fₑ : A.symm.fₑ ∘ A.fₑ = id := by
  ext e
  simp only [Function.comp_apply, symm_fₑ_fₑ, id_eq]

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma fₑ_comp_symm_fₑ : A.fₑ ∘ A.symm.fₑ = id := by
  ext e
  simp [Function.comp_apply, fₑ_symm_fₑ, id_eq]

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma refl_symm : (Isom.refl G).symm = Isom.refl G := by
  ext <;> simp [refl_fᵥ, Equiv.refl_apply]
  · apply_fun (refl G).fᵥ using (refl G).fᵥinj
    simp
  · apply_fun (refl G).fₑ using (refl G).fₑinj
    simp

def trans (B : H ≃ᴳ I) : G ≃ᴳ I where
  toEmb := A.toEmb.trans B.toEmb
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

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma refl_trans : (Isom.refl G).trans A = A := by
  ext <;> simp [trans_fᵥ, trans_fₑ, Equiv.refl_apply]

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma trans_refl : A.trans (Isom.refl H) = A := by
  ext <;> simp [trans_fᵥ, trans_fₑ, Equiv.refl_apply]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma trans_symm (B : H ≃ᴳ I) : (A.trans B).symm = B.symm.trans A.symm := by
  ext <;> simp [symm_fᵥ, symm_fₑ, Equiv.symm_apply_apply]

lemma canGo_iff (u : V) (e : E) (v : V) :
    H.canGo (A.fᵥ u) (A.fₑ e) (A.fᵥ v) ↔ G.canGo u e v := Emb.canGo_iff A.toEmb u e v

lemma adj_iff (u v : V) : H.adj (A.fᵥ u) (A.fᵥ v) ↔ G.adj u v := by
  refine ⟨?_, A.toEmb.adj⟩
  rintro h
  convert A.symm.toEmb.adj h <;> simp only [symm_fᵥ, Equiv.ofBijective_symm_apply_apply]

end Isom

noncomputable def Hom.Isom (A : Hom G H) (B : G ≃ᴳ I) (C : H ≃ᴳ J) : Hom I J where
  fᵥ := C.fᵥ ∘ A.fᵥ ∘ B.symm.fᵥ
  fₑ := C.fₑ ∘ A.fₑ ∘ B.symm.fₑ
  inc e := by
    simp only [Function.comp_apply, map_comp]
    rw [C.inc, A.inc, B.symm.inc]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq V'] in @[simp]
lemma Hom.Isom_fᵥ (A : Hom G H) (B : G ≃ᴳ I) (C : H ≃ᴳ J) :
    (A.Isom B C).fᵥ = C.fᵥ ∘ A.fᵥ ∘ B.symm.fᵥ := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq V'] in @[simp]
lemma Hom.Isom_fₑ (A : Hom G H) (B : G ≃ᴳ I) (C : H ≃ᴳ J) :
    (A.Isom B C).fₑ = C.fₑ ∘ A.fₑ ∘ B.symm.fₑ := rfl

noncomputable def Emb.Isom (A : G ⊆ᴳ H) (B : G ≃ᴳ I) (C : H ≃ᴳ J) : I ⊆ᴳ J where
  toHom := A.toHom.Isom B C
  fᵥinj v w h := by
    simp only [Hom.Isom_fᵥ, Function.comp_apply] at h
    rwa [C.fᵥinj.eq_iff, A.fᵥinj.eq_iff, B.symm.fᵥinj.eq_iff] at h
  fₑinj e f h := by
    simp only [Hom.Isom_fₑ, Function.comp_apply] at h
    rwa [C.fₑinj.eq_iff, A.fₑinj.eq_iff, B.symm.fₑinj.eq_iff] at h

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq V'] in @[simp]
lemma Emb.Isom_fᵥ (A : G ⊆ᴳ H) (B : G ≃ᴳ I) (C : H ≃ᴳ J) :
    (A.Isom B C).fᵥ = C.fᵥ ∘ A.fᵥ ∘ B.symm.fᵥ := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq V'] in @[simp]
lemma Emb.Isom_fₑ (A : G ⊆ᴳ H) (B : G ≃ᴳ I) (C : H ≃ᴳ J) :
    (A.Isom B C).fₑ = C.fₑ ∘ A.fₑ ∘ B.symm.fₑ := rfl

noncomputable def SpanningEmb.Isom (A : SpanningEmb G H) (B : G ≃ᴳ I) (C : H ≃ᴳ J) :
    SpanningEmb I J where
  toEmb := A.toEmb.Isom B C
  fᵥsurj v := by
    simp only [Emb.Isom_fᵥ, Function.comp_apply]
    use B.fᵥ (A.fᵥEquiv.symm (C.symm.fᵥ v))
    rw [B.symm_fᵥ, ← A.fᵥEquiv_apply, ← C.fᵥEquiv_apply, C.symm_fᵥ]
    simp only [Equiv.ofBijective_symm_apply_apply, Equiv.apply_symm_apply]


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
    ext <;> simp only [Isom.trans_fᵥ, Function.comp_apply, Isom.fᵥ_symm_fᵥ, Isom.refl_fᵥ,
      Equiv.refl_apply, Isom.trans_fₑ, Isom.fₑ_symm_fₑ, Isom.refl_fₑ]

end Aut


def map (fᵥ : V → W) (fₑ : F → E) : Graph W F where
  inc e := G.inc (fₑ e) |>.map fᵥ

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma map_inc (fᵥ : V → W) (fₑ : F → E) (e : F) :
  (G.map fᵥ fₑ).inc e = (G.inc (fₑ e) |>.map fᵥ) := rfl

def Hom.range (A : Hom G H) : Graph (Set.range A.fᵥ) (Set.range A.fₑ) where
  inc e := (H.inc e).pmap (Subtype.mk) (by
    rintro u hu
    have : e = (A.fₑ (Set.rangeSplitting A.fₑ e)) :=
      (Set.apply_rangeSplitting A.fₑ e).symm
    rw [this, A.inc, mem_map_iff] at hu
    obtain ⟨e', he', rfl⟩ := hu
    exact Set.mem_range_self e')

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma Hom.range_inc_val (A : Hom G H) (e : Set.range A.fₑ) :
    (A.range.inc e).map Subtype.val = H.inc e := by
  unfold Hom.range
  simp only [pmap_subtype_map_val]

def Hom.range_Emb (A : Hom G H) : A.range ⊆ᴳ H where
  fᵥ := Subtype.val
  fₑ := Subtype.val
  inc e := by
    change _ = ((A.range.inc e).map Subtype.val)
    rw [range_inc_val]
  fᵥinj v w h := by
    ext
    simpa only [range, Set.rangeFactorization_coe] using h
  fₑinj e f h := by
    ext
    simpa only [range, Set.rangeFactorization_coe] using h

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma Hom.range_Emb_fᵥ (A : Hom G H) : (A.range_Emb).fᵥ = Subtype.val := rfl

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma Hom.range_Emb_fₑ (A : Hom G H) : (A.range_Emb).fₑ = Subtype.val := rfl

def Hom.range.Isom (A : Hom G H) (B : G ≃ᴳ I) (C : H ≃ᴳ J) : A.range ≃ᴳ (A.Isom B C).range where
  fᵥ v := ⟨C.fᵥ v.val, (by
    obtain ⟨_, v, rfl⟩ := v
    use B.fᵥEquiv v
    simp only [Equiv.ofBijective_apply, Isom_fᵥ, B.symm_fᵥ, Function.comp_apply,
      Equiv.ofBijective_symm_apply_apply])⟩
  fₑ e := ⟨C.fₑ e.val, (by
    obtain ⟨_, e, rfl⟩ := e
    use B.fₑEquiv e
    simp only [Equiv.ofBijective_apply, Isom_fₑ, B.symm_fₑ, Function.comp_apply,
      Equiv.ofBijective_symm_apply_apply])⟩
  inc e := by
    simp only [subtype_eq, ← map_comp, (A.Isom B C).range_inc_val, C.inc]
    have := (A.range_Emb).inc e
    simp only [range_Emb_fₑ, range_Emb_fᵥ] at this
    rw [this, ← map_comp]; clear this
    congr
  fᵥinj v w h := by
    ext
    simpa only [Isom_fᵥ, Subtype.mk.injEq, C.fᵥinj.eq_iff] using h
  fₑinj e f h := by
    ext
    simpa only [Isom_fₑ, Subtype.mk.injEq, C.fₑinj.eq_iff] using h
  fᵥsurj v := by
    obtain ⟨u, hu⟩ := v.property
    simp only [Isom_fᵥ, Subtype.exists, Set.mem_range, Function.comp_apply] at hu ⊢
    use A.fᵥ (B.symm.fᵥ u)
    constructor
    · ext
      simpa only
    · use B.symm.fᵥ u
  fₑsurj e := by
    obtain ⟨u, hu⟩ := e.property
    simp only [Isom_fₑ, Subtype.exists, Set.mem_range, Function.comp_apply] at hu ⊢
    use A.fₑ (B.symm.fₑ u)
    constructor
    · ext
      simpa only
    · use B.symm.fₑ u

def Hom.rangeFactorization (A : Hom G H) : Hom G A.range where
  fᵥ := Set.rangeFactorization A.fᵥ
  fₑ := Set.rangeFactorization A.fₑ
  inc e := by
    simp only [range, Set.rangeFactorization_coe, subtype_eq, pmap_subtype_map_val, ← map_comp,
      Set.coe_comp_rangeFactorization]
    exact A.inc e

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma Hom.rangeFactorization_fᵥ (A : Hom G H) :
    (A.rangeFactorization).fᵥ = Set.rangeFactorization A.fᵥ := rfl

omit [DecidableEq V] [DecidableEq W] in @[simp]
lemma Hom.rangeFactorization_fₑ (A : Hom G H) :
    (A.rangeFactorization).fₑ = Set.rangeFactorization A.fₑ := rfl

def Emb.range_Isom (A : G ⊆ᴳ H) : G ≃ᴳ A.range where
  fᵥ := Set.rangeFactorization A.fᵥ
  fₑ := Set.rangeFactorization A.fₑ
  inc e := by
    simp only [Hom.range, Set.rangeFactorization_coe, subtype_eq, pmap_subtype_map_val, ← map_comp,
      Set.coe_comp_rangeFactorization]
    exact A.inc e
  fᵥinj v w h := by
    apply_fun (·.val) at h
    simp only [Set.rangeFactorization_coe] at h
    exact A.fᵥinj h
  fₑinj e f h := by
    apply_fun (·.val) at h
    simp only [Set.rangeFactorization_coe] at h
    exact A.fₑinj h
  fᵥsurj v := by
    obtain ⟨u, hu⟩ := v.property
    use u
    ext
    exact hu
  fₑsurj e := by
    obtain ⟨e', he'⟩ := e.property
    use e'
    ext
    exact he'

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb.range_Isom_fᵥ (A : G ⊆ᴳ H) :
    (A.range_Isom).fᵥ = Set.rangeFactorization A.fᵥ := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb.range_Isom_fₑ (A : G ⊆ᴳ H) :
    (A.range_Isom).fₑ = Set.rangeFactorization A.fₑ := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb.range_Isom_symm_fᵥ (A : G ⊆ᴳ H) :
    (A.range_Isom).symm.fᵥ = Set.rangeSplitting A.fᵥ := by
  ext v
  apply_fun Set.rangeFactorization A.fᵥ using (Set.rangeFactorization_injective_iff A.fᵥ).mpr A.fᵥinj
  rw [Set.leftInverse_rangeSplitting A.fᵥ v]
  change (A.range_Isom).fᵥ (A.range_Isom.symm.fᵥ v) = v
  rw [Isom.fᵥ_symm_fᵥ]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb.range_Isom_symm_fₑ (A : G ⊆ᴳ H) :
    (A.range_Isom).symm.fₑ = Set.rangeSplitting A.fₑ := by
  ext e
  apply_fun Set.rangeFactorization A.fₑ using (Set.rangeFactorization_injective_iff A.fₑ).mpr A.fₑinj
  rw [Set.leftInverse_rangeSplitting A.fₑ e]
  change (A.range_Isom).fₑ (A.range_Isom.symm.fₑ e) = e
  rw [Isom.fₑ_symm_fₑ]

-- def Subtype_Emb_Subtype_of_imp {vp₁ vp₂ : V → Prop} {ep₁ ep₂ : E → Prop}
--     {G : Graph (Subtype vp₁) (Subtype ep₁)} {H : Graph (Subtype vp₂) (Subtype ep₂)}
--     (hv : vp₁ ≤ vp₂) (he : ep₁ ≤ ep₂) : G ⊆ᴳ H := by
--   refine Emb.OfEmbs (Subtype.impEmbedding _ _ hv) (Subtype.impEmbedding _ _ he) ?_
--   rintro ⟨f, hf⟩
--   simp only [subtype_eq]

def union (A : Hom G I) (B : Hom H I) :
    Graph (Set.range (A.add B).fᵥ) (Set.range (A.add B).fₑ) := (A.add B).range

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma union_inc_val (A : Hom G I) (B : Hom H I) (e : Set.range (A.add B).fₑ) :
    ((union A B).inc e).map Subtype.val = I.inc e := by
  unfold union
  rw [Hom.range_inc_val]

def Hom1_union (A : Hom G I) (B : Hom H I) : Hom G (union A B) where
  fᵥ := Set.rangeFactorization (A.add B).fᵥ ∘ Sum.inl
  fₑ := Set.rangeFactorization (A.add B).fₑ ∘ Sum.inl
  inc e := by
    rw [subtype_eq]
    conv_lhs => simp only [Function.comp_apply, union_inc_val, Set.rangeFactorization_coe,
      Hom.add_fₑ_inl_apply, map_comp]
    conv_rhs => simp only [← map_comp, ← Function.comp_assoc, Set.coe_comp_rangeFactorization,
      Hom.add_fᵥ_inl]
    exact A.inc e

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Hom1_union_fᵥ (A : Hom G I) (B : Hom H I) :
    (Hom1_union A B).fᵥ = Set.rangeFactorization (A.add B).fᵥ ∘ Sum.inl := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Hom1_union_fₑ (A : Hom G I) (B : Hom H I) :
    (Hom1_union A B).fₑ = Set.rangeFactorization (A.add B).fₑ ∘ Sum.inl := rfl

def Emb1_union (A : Emb G I) (B : Hom H I) : G ⊆ᴳ union A.toHom B where
  toHom := Hom1_union A.toHom B
  fᵥinj v w h := by
    apply_fun (·.val) at h
    simp only [Hom1_union, Function.comp_apply, Set.rangeFactorization_coe,
      Hom.add_fᵥ_inl_apply] at h
    exact A.fᵥinj h
  fₑinj e f h := by
    apply_fun (·.val) at h
    simp only [Hom1_union, Function.comp_apply, Set.rangeFactorization_coe,
      Hom.add_fₑ_inl_apply] at h
    exact A.fₑinj h

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb1_union_fᵥ (A : Emb G I) (B : Hom H I) :
    (Emb1_union A B).fᵥ = Set.rangeFactorization (A.toHom.add B).fᵥ ∘ Sum.inl := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb1_union_fₑ (A : Emb G I) (B : Hom H I) :
    (Emb1_union A B).fₑ = Set.rangeFactorization (A.toHom.add B).fₑ ∘ Sum.inl := rfl

def Hom2_union (A : Hom G I) (B : Hom H I) : Hom H (union A B) where
  fᵥ := Set.rangeFactorization (A.add B).fᵥ ∘ Sum.inr
  fₑ := Set.rangeFactorization (A.add B).fₑ ∘ Sum.inr
  inc e := by
    rw [subtype_eq]
    conv_lhs => simp
    conv_rhs => simp [← map_comp, ← Function.comp_assoc]
    exact B.inc e

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Hom2_union_fᵥ (A : Hom G I) (B : Hom H I) :
    (Hom2_union A B).fᵥ = Set.rangeFactorization (A.add B).fᵥ ∘ Sum.inr := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Hom2_union_fₑ (A : Hom G I) (B : Hom H I) :
    (Hom2_union A B).fₑ = Set.rangeFactorization (A.add B).fₑ ∘ Sum.inr := rfl

def Emb2_union (A : Hom G I) (B : Emb H I) : H ⊆ᴳ union A B.toHom where
  toHom := Hom2_union A B.toHom
  fᵥinj v w h := by
    apply_fun (·.val) at h
    simp only [Hom2_union, Function.comp_apply, Set.rangeFactorization_coe,
      Hom.add_fᵥ_inr_apply] at h
    exact B.fᵥinj h
  fₑinj e f h := by
    apply_fun (·.val) at h
    simp only [Hom2_union, Function.comp_apply, Set.rangeFactorization_coe,
      Hom.add_fₑ_inr_apply] at h
    exact B.fₑinj h

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb2_union_fᵥ (A : Hom G I) (B : Emb H I) :
    (Emb2_union A B).fᵥ = Set.rangeFactorization (A.add B.toHom).fᵥ ∘ Sum.inr := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb2_union_fₑ (A : Hom G I) (B : Emb H I) :
    (Emb2_union A B).fₑ = Set.rangeFactorization (A.add B.toHom).fₑ ∘ Sum.inr := rfl

def union_Emb (A : Hom G I) (B : Hom H I) : union A B ⊆ᴳ I where
  fᵥ := Subtype.val
  fₑ := Subtype.val
  inc e := by
    change _ = ((union A B).inc e).map Subtype.val
    rw [union, Hom.range_inc_val]
  fᵥinj v w h := by
    simp only [union, pmap_subtype_map_val] at h
    ext
    exact h
  fₑinj e f h := by
    simp only [union, pmap_subtype_map_val] at h
    ext
    exact h

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma union_Emb_fᵥ (A : Hom G I) (B : Hom H I) :
    (union_Emb A B).fᵥ = Subtype.val := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma union_Emb_fₑ (A : Hom G I) (B : Hom H I) :
    (union_Emb A B).fₑ = Subtype.val := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Hom1_union_trans_union_Emb (A : Hom G I) (B : Hom H I) :
    (Hom1_union A B).trans (union_Emb A B).toHom = A := by
  ext v
  · simp only [union_Emb, Hom.trans_fᵥ, Hom1_union_fᵥ, Function.comp_apply,
    Set.rangeFactorization_coe, Hom.add_fᵥ_inl_apply]
  · simp only [union_Emb, Hom.trans_fₑ, Hom1_union_fₑ, Function.comp_apply,
    Set.rangeFactorization_coe, Hom.add_fₑ_inl_apply]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb1_union_trans_union_Emb (A : G ⊆ᴳ I) (B : Hom H I) :
    (Emb1_union A B).trans (union_Emb A.toHom B) = A := by
  ext v
  · simp only [union_Emb, Emb.trans_fᵥ, Emb1_union_fᵥ, Function.comp_apply,
    Set.rangeFactorization_coe, Hom.add_fᵥ_inl_apply]
  · simp only [union_Emb, Emb.trans_fₑ, Emb1_union_fₑ, Function.comp_apply,
    Set.rangeFactorization_coe, Hom.add_fₑ_inl_apply]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Hom2_union_trans_union_Emb (A : Hom G I) (B : Hom H I) :
    (Hom2_union A B).trans (union_Emb A B).toHom = B := by
  ext v
  · simp only [union_Emb, Hom.trans_fᵥ, Hom2_union_fᵥ, Function.comp_apply,
    Set.rangeFactorization_coe, Hom.add_fᵥ_inr_apply]
  · simp only [union_Emb, Hom.trans_fₑ, Hom2_union_fₑ, Function.comp_apply,
    Set.rangeFactorization_coe, Hom.add_fₑ_inr_apply]


def inter (A : Hom G I) (B : Hom H I) :
  Graph (Set.range A.fᵥ ∩ Set.range B.fᵥ).Elem (Set.range A.fₑ ∩ Set.range B.fₑ).Elem where
  inc e := (I.inc (e.val)).pmap (Subtype.mk) (by
      rintro u hu
      obtain ⟨e, ⟨a, heA⟩, b, heB⟩ := e
      simp only [Set.mem_inter_iff, Set.mem_range]
      constructor
      · subst heA
        simp only [A.inc, mem_map_iff] at hu
        obtain ⟨e', he', rfl⟩ := hu
        exact exists_apply_eq_apply _ _
      · subst heB
        simp only [B.inc, mem_map_iff] at hu
        obtain ⟨e', he', rfl⟩ := hu
        exact exists_apply_eq_apply _ _
      )

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma inter_inc_val (A : Hom G I) (B : Hom H I) (e : (Set.range A.fₑ ∩ Set.range B.fₑ).Elem) :
    ((inter A B).inc e).map Subtype.val = I.inc e := by
  unfold inter
  simp only [pmap_subtype_map_val]

def inter_Emb (A : Hom G I) (B : Hom H I) : inter A B ⊆ᴳ I where
  fᵥ := Subtype.val
  fₑ := Subtype.val
  inc e := by
    change _ = ((inter A B).inc e).map Subtype.val
    rw [inter_inc_val]
  fᵥinj v w h := by
    simp only [inter, pmap_subtype_map_val] at h
    ext
    exact h
  fₑinj e f h := by
    simp only [inter, pmap_subtype_map_val] at h
    ext
    exact h

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma inter_Emb_fᵥ (A : Hom G I) (B : Hom H I) :
    (inter_Emb A B).fᵥ = Subtype.val := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma inter_Emb_fₑ (A : Hom G I) (B : Hom H I) :
    (inter_Emb A B).fₑ = Subtype.val := rfl

def inter_Emb_range1 (A : Hom G I) (B : Hom H I) : inter A B ⊆ᴳ A.range := by
  apply Emb.OfEmbs (Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_left))
    (Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_left))
  intro e
  simp only [subtype_eq, Hom.range_inc_val, Subtype.impEmbedding_apply_coe, ← map_comp,
    Subtype.val_comp_impEmbedding, inter_inc_val]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma inter_Emb_range1_fᵥ (A : Hom G I) (B : Hom H I) :
    (inter_Emb_range1 A B).fᵥ =
    Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_left) := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma inter_Emb_range1_fₑ (A : Hom G I) (B : Hom H I) :
    (inter_Emb_range1 A B).fₑ =
    Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_left) := rfl

def inter_Emb_range2 (A : Hom G I) (B : Hom H I) : inter A B ⊆ᴳ B.range := by
  apply Emb.OfEmbs (Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_right))
    (Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_right))
  intro e
  simp only [subtype_eq, Hom.range_inc_val, Subtype.impEmbedding_apply_coe, ← map_comp,
    Subtype.val_comp_impEmbedding, inter_inc_val]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma inter_Emb_range2_fᵥ (A : Hom G I) (B : Hom H I) :
    (inter_Emb_range2 A B).fᵥ =
    Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_right) := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma inter_Emb_range2_fₑ (A : Hom G I) (B : Hom H I) :
    (inter_Emb_range2 A B).fₑ =
    Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_right) := rfl

noncomputable def inter_Emb1 (A : G ⊆ᴳ I) (B : Hom H I) : (inter A.toHom B) ⊆ᴳ G :=
  (inter_Emb_range1 A.toHom B).Isom (Isom.refl _) A.range_Isom.symm

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma inter_Emb1_fᵥ (A : G ⊆ᴳ I) (B : Hom H I) :
    (inter_Emb1 A B).fᵥ =
    (Set.rangeSplitting A.fᵥ) ∘ Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_left) := by
  simp only [inter_Emb1, Emb.Isom_fᵥ, Emb.range_Isom_symm_fᵥ,
    inter_Emb_range1_fᵥ, Isom.refl_symm, Isom.refl_fᵥ, Equiv.coe_refl, CompTriple.comp_eq]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma mem_range_inter_Emb1_fᵥ (A : G ⊆ᴳ I) (B : Hom H I) (v : _) :
    v ∈ Set.range (inter_Emb1 A B).fᵥ ↔ A.fᵥ v ∈ Set.range B.fᵥ := by
  simp only [inter_Emb1_fᵥ, Set.mem_range, Function.comp_apply, Subtype.exists,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨u, ⟨⟨v, rfl⟩, w, hw⟩, rfl⟩
    use w
    convert hw
    rw [Set.rangeSplitting_eq_iff A.fᵥinj]
    rfl
  · rintro ⟨w, hw⟩
    use A.fᵥ v, ?_
    simp only [Set.rangeSplitting_eq_iff A.fᵥinj, Subtype.impEmbedding_apply_coe]
    refine ⟨⟨v, rfl⟩, ⟨w, hw⟩⟩

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma inter_Emb1_fₑ (A : G ⊆ᴳ I) (B : Hom H I) :
    (inter_Emb1 A B).fₑ =
    (Set.rangeSplitting A.fₑ) ∘ Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_left) := by
  simp only [inter_Emb1, Emb.Isom_fₑ, Emb.range_Isom_symm_fₑ,
    inter_Emb_range1_fₑ, Isom.refl_symm, Isom.refl_fₑ, Equiv.coe_refl, CompTriple.comp_eq]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma mem_range_inter_Emb1_fₑ (A : G ⊆ᴳ I) (B : Hom H I) (e : E) :
    e ∈ Set.range (inter_Emb1 A B).fₑ ↔ A.fₑ e ∈ Set.range B.fₑ := by
  simp only [inter_Emb1_fₑ, Set.mem_range, Function.comp_apply, Subtype.exists,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨u, ⟨⟨v, rfl⟩, f, hf⟩, rfl⟩
    use f
    convert hf
    rw [Set.rangeSplitting_eq_iff A.fₑinj]
    rfl
  · rintro ⟨f, hf⟩
    use A.fₑ e, ?_
    simp only [Set.rangeSplitting_eq_iff A.fₑinj, Subtype.impEmbedding_apply_coe]
    refine ⟨⟨e, rfl⟩, ⟨f, hf⟩⟩

noncomputable def inter_Emb2 (A : Hom G I) (B : H ⊆ᴳ I) : (inter A B.toHom) ⊆ᴳ H :=
  (inter_Emb_range2 A B.toHom).Isom (Isom.refl _) B.range_Isom.symm

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma inter_Emb2_fᵥ (A : Hom G I) (B : H ⊆ᴳ I) :
    (inter_Emb2 A B).fᵥ =
    (Set.rangeSplitting B.fᵥ) ∘ Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_right) := by
  simp only [inter_Emb2, Emb.Isom_fᵥ, Emb.range_Isom_symm_fᵥ,
    inter_Emb_range2_fᵥ, Isom.refl_symm, Isom.refl_fᵥ, Equiv.coe_refl, CompTriple.comp_eq]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma mem_range_inter_Emb2_fᵥ (A : Hom G I) (B : H ⊆ᴳ I) (w : _) :
    w ∈ Set.range (inter_Emb2 A B).fᵥ ↔ B.fᵥ w ∈ Set.range A.fᵥ := by
  simp only [inter_Emb2_fᵥ, Set.mem_range, Function.comp_apply, Subtype.exists,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨u, ⟨⟨v, rfl⟩, w, hw⟩, rfl⟩
    use v
    nth_rewrite 1 [← hw]
    rw [B.fᵥinj.eq_iff, eq_comm, Set.rangeSplitting_eq_iff B.fᵥinj, hw]
    rfl
  · rintro ⟨v, hv⟩
    use A.fᵥ v, ?_
    simpa only [Set.rangeSplitting_eq_iff B.fᵥinj, Subtype.impEmbedding_apply_coe]
    refine ⟨⟨v, rfl⟩, ⟨w, hv.symm⟩⟩

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma inter_Emb2_fₑ (A : Hom G I) (B : H ⊆ᴳ I) :
    (inter_Emb2 A B).fₑ =
    (Set.rangeSplitting B.fₑ) ∘ Subtype.impEmbedding _ _ (fun _ => Set.mem_of_mem_inter_right) := by
  simp only [inter_Emb2, Emb.Isom_fₑ, Emb.range_Isom_symm_fₑ,
    inter_Emb_range2_fₑ, Isom.refl_symm, Isom.refl_fₑ, Equiv.coe_refl, CompTriple.comp_eq]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma mem_range_inter_Emb2_fₑ (A : Hom G I) (B : H ⊆ᴳ I) (f : _) :
    f ∈ Set.range (inter_Emb2 A B).fₑ ↔ B.fₑ f ∈ Set.range A.fₑ := by
  simp only [inter_Emb2_fₑ, Set.mem_range, Function.comp_apply, Subtype.exists,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨u, ⟨⟨v, rfl⟩, e, he⟩, rfl⟩
    use v
    nth_rewrite 1 [← he]
    rw [B.fₑinj.eq_iff, eq_comm, Set.rangeSplitting_eq_iff B.fₑinj, he]
    rfl
  · rintro ⟨v, hv⟩
    use A.fₑ v, ?_
    simpa only [Set.rangeSplitting_eq_iff B.fₑinj, Subtype.impEmbedding_apply_coe]
    refine ⟨⟨v, rfl⟩, ⟨f, hv.symm⟩⟩

/--
The 'inter' function above can be thought of as defining an intersection of two graphs in the
presence of a mutual supergraph.

The 'glue' function below is a reverse of that: Given a mutual subgraph of two graphs,
it constructs a union of the two graphs by gluing on the mutual subgraph.
-/
noncomputable def Emb.glue (A : G ⊆ᴳ H) (B : G ⊆ᴳ I) :
  Graph (W ⊕ (Set.range B.fᵥ)ᶜ.Elem) (F ⊕ (Set.range B.fₑ)ᶜ.Elem) :=
  let fᵥ : _ → W ⊕ (Set.range B.fᵥ)ᶜ.Elem := (λ v => match v with
    | Sum.inl v₁ => Sum.inl v₁
    | Sum.inr v₂ => by
      by_cases h : v₂ ∈ Set.range B.fᵥ
      · exact Sum.inl (A.fᵥ (Set.rangeSplitting B.fᵥ ⟨v₂, h⟩))
      · exact Sum.inr ⟨v₂, by simp only [Set.mem_compl_iff, h, not_false_eq_true]⟩)
  let fₑ : F ⊕ (Set.range B.fₑ)ᶜ.Elem → F ⊕ E' := fun e => match e with
    | Sum.inl e₁ => Sum.inl e₁
    | Sum.inr e₂ => Sum.inr e₂.val
  (H + I).map fᵥ fₑ

def Emb1_glue (A : G ⊆ᴳ H) (B : G ⊆ᴳ I) : H ⊆ᴳ A.glue B where
  fᵥ := Sum.inl
  fₑ := Sum.inl
  inc e := by
    unfold Emb.glue
    simp only [map, Set.mem_range, add_inc]
    rw [← map_comp]
    congr
  fᵥinj v w h := by simpa only [Sum.inl.injEq] using h
  fₑinj e f h := by simpa only [Sum.inl.injEq] using h

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb1_glue_fᵥ (A : G ⊆ᴳ H) (B : G ⊆ᴳ I) :
    (Emb1_glue A B).fᵥ = Sum.inl := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb1_glue_fₑ (A : G ⊆ᴳ H) (B : G ⊆ᴳ I) :
    (Emb1_glue A B).fₑ = Sum.inl := rfl

noncomputable def Emb2_glue (A : G ⊆ᴳ H) (B : G ⊆ᴳ I) : I ⊆ᴳ A.glue B where
  fᵥ v := by
    by_cases hv : v ∈ Set.range B.fᵥ
    · exact Sum.inl (A.fᵥ (Set.rangeSplitting B.fᵥ ⟨v, hv⟩))
    · exact Sum.inr ⟨v, by simp only [Set.mem_compl_iff, hv, not_false_eq_true]⟩
  fₑ e := by
    by_cases he : e ∈ Set.range B.fₑ
    · exact Sum.inl (A.fₑ (Set.rangeSplitting B.fₑ ⟨e, he⟩))
    · exact Sum.inr ⟨e, by simp only [Set.mem_compl_iff, he, not_false_eq_true]⟩
  inc e := by
    unfold Emb.glue
    by_cases he : e ∈ Set.range B.fₑ <;> simp only [map, Set.mem_range, add_inc, he, ↓reduceDIte]
    · obtain ⟨e', rfl⟩ := he
      rw [A.inc, B.inc, Set.rangeSplitting_apply' B.fₑinj]
      repeat rw [← map_comp]
      congr
      ext v
      simp only [Set.mem_range, Function.comp_apply, exists_apply_eq_apply, ↓reduceDIte,
        Set.rangeSplitting_apply' B.fᵥinj]
    · rw [← map_comp]
      congr
  fᵥinj v w h := by
    by_cases hv : v ∈ Set.range B.fᵥ <;> by_cases hw : w ∈ Set.range B.fᵥ <;> simp_all [dite_false,
      Sum.inr.injEq, Subtype.mk.injEq, not_false_eq_true, Set.mem_range, not_exists]
    rw [A.fᵥinj.eq_iff, (Set.rangeSplitting_injective B.fᵥ).eq_iff] at h
    simpa only [Subtype.mk.injEq] using h
  fₑinj e f h := by
    by_cases he : e ∈ Set.range B.fₑ <;> by_cases hf : f ∈ Set.range B.fₑ <;> simp_all [dite_false,
      Sum.inr.injEq, Subtype.mk.injEq, not_false_eq_true, Set.mem_range, not_exists]
    rw [A.fₑinj.eq_iff, (Set.rangeSplitting_injective B.fₑ).eq_iff] at h
    simpa only [Subtype.mk.injEq] using h

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb2_glue_fᵥ (A : G ⊆ᴳ H) (B : G ⊆ᴳ I) :
    (Emb2_glue A B).fᵥ = (fun v => by
    by_cases hv : v ∈ Set.range B.fᵥ
    · exact Sum.inl (A.fᵥ (Set.rangeSplitting B.fᵥ ⟨v, hv⟩))
    · exact Sum.inr ⟨v, by simp only [Set.mem_compl_iff, hv, not_false_eq_true]⟩) := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] in @[simp]
lemma Emb2_glue_fₑ (A : G ⊆ᴳ H) (B : G ⊆ᴳ I) :
    (Emb2_glue A B).fₑ = (fun e => by
    by_cases he : e ∈ Set.range B.fₑ
    · exact Sum.inl (A.fₑ (Set.rangeSplitting B.fₑ ⟨e, he⟩))
    · exact Sum.inr ⟨e, by simp only [Set.mem_compl_iff, he, not_false_eq_true]⟩) := rfl

def glue_Emb_of_Emb (A : G ⊆ᴳ H) (B : G ⊆ᴳ I) (C : H ⊆ᴳ J) (D : I ⊆ᴳ J)
    (hᵥ : C.fᵥ ∘ A.fᵥ = D.fᵥ ∘ B.fᵥ) (hₑ : C.fₑ ∘ A.fₑ = D.fₑ ∘ B.fₑ)
    (hᵥ' : Set.range C.fᵥ ∩ Set.range D.fᵥ = Set.range (C.fᵥ ∘ A.fᵥ))
    (hₑ' : Set.range C.fₑ ∩ Set.range D.fₑ = Set.range (C.fₑ ∘ A.fₑ)) :
    (A.glue B) ⊆ᴳ J where
  fᵥ v := by
    match v with
    | Sum.inl v => exact C.fᵥ v
    | Sum.inr v => exact D.fᵥ v.val
  fₑ e := by
    match e with
    | Sum.inl e => exact C.fₑ e
    | Sum.inr e => exact D.fₑ e.val
  inc e := by
    match e with
    | Sum.inl e =>
      simp [Emb.glue, C.inc]
      repeat rw [← map_comp]
      congr
    | Sum.inr e =>
      simp [Emb.glue, D.inc]
      repeat rw [← map_comp]
      congr
      ext u
      simp
      split_ifs with hu
      · simp [hu]
        rw [← Function.comp_apply (f := C.fᵥ), hᵥ]
        simp [D.fᵥinj.eq_iff, Set.apply_rangeSplitting]
      case neg =>
        simp [hu]
  fᵥinj v w hvw := by
    match v, w with
    | Sum.inl v, Sum.inl w =>
      rw [C.fᵥinj.eq_iff] at hvw
      rw [hvw]
    | Sum.inl v, Sum.inr ⟨w, hw⟩ =>
      exfalso
      simp [Emb.glue, Set.mem_range, map, add_inc, C.inc, Sum.inl.injEq] at hvw hw hᵥ'
      have : C.fᵥ v ∈ Set.range C.fᵥ ∩ Set.range D.fᵥ := by
        simp
        rw [hvw]
        simp
      rw [hᵥ', hᵥ, hvw] at this
      simp [D.fᵥinj.eq_iff, hw] at this
    | Sum.inr ⟨v, hv⟩, Sum.inl w =>
      exfalso
      simp [Emb.glue, Set.mem_range, map, add_inc, C.inc, Sum.inl.injEq] at hvw hv hᵥ'
      have : D.fᵥ v ∈ Set.range C.fᵥ ∩ Set.range D.fᵥ := by
        simp
        rw [hvw]
        simp
      rw [hᵥ', hᵥ] at this
      simp [D.fᵥinj.eq_iff, hv] at this
    | Sum.inr ⟨v, hv⟩, Sum.inr ⟨w, hw⟩ => simp_all [D.fᵥinj.eq_iff]
  fₑinj e f hef := by
    match e, f with
    | Sum.inl e, Sum.inl f => simp_all [C.fₑinj.eq_iff]
    | Sum.inl e, Sum.inr ⟨f, hf⟩ =>
      exfalso
      simp [Emb.glue, Set.mem_range, map, add_inc, C.inc, Sum.inl.injEq] at hef hf hₑ'
      have : C.fₑ e ∈ Set.range C.fₑ ∩ Set.range D.fₑ := by
        simp
        rw [hef]
        simp
      rw [hₑ', hₑ, hef] at this
      simp [D.fₑinj.eq_iff, hf] at this
    | Sum.inr ⟨e, he⟩, Sum.inl f =>
      exfalso
      simp [Emb.glue, Set.mem_range, map, add_inc, C.inc, Sum.inl.injEq] at hef he hₑ'
      have : D.fₑ e ∈ Set.range C.fₑ ∩ Set.range D.fₑ := by
        simp
        rw [hef]
        simp
      rw [hₑ', hₑ] at this
      simp [D.fₑinj.eq_iff, he] at this
    | Sum.inr e, Sum.inr f => simp_all [D.fₑinj.eq_iff, Subtype.val_inj]

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq V'] in @[simp]
lemma glue_Emb_of_Emb_fᵥ (A : G ⊆ᴳ H) (B : G ⊆ᴳ I) (C : H ⊆ᴳ J) (D : I ⊆ᴳ J)
    (hᵥ : C.fᵥ ∘ A.fᵥ = D.fᵥ ∘ B.fᵥ) (hₑ : C.fₑ ∘ A.fₑ = D.fₑ ∘ B.fₑ)
    (hᵥ' : Set.range C.fᵥ ∩ Set.range D.fᵥ = Set.range (C.fᵥ ∘ A.fᵥ))
    (hₑ' : Set.range C.fₑ ∩ Set.range D.fₑ = Set.range (C.fₑ ∘ A.fₑ)) :
    (glue_Emb_of_Emb A B C D hᵥ hₑ hᵥ' hₑ').fᵥ = (fun v => by
    match v with
    | Sum.inl v => exact C.fᵥ v
    | Sum.inr v => exact D.fᵥ v.val) := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq V'] in @[simp]
lemma glue_Emb_of_Emb_fₑ (A : G ⊆ᴳ H) (B : G ⊆ᴳ I) (C : H ⊆ᴳ J) (D : I ⊆ᴳ J)
    (hᵥ : C.fᵥ ∘ A.fᵥ = D.fᵥ ∘ B.fᵥ) (hₑ : C.fₑ ∘ A.fₑ = D.fₑ ∘ B.fₑ)
    (hᵥ' : Set.range C.fᵥ ∩ Set.range D.fᵥ = Set.range (C.fᵥ ∘ A.fᵥ))
    (hₑ' : Set.range C.fₑ ∩ Set.range D.fₑ = Set.range (C.fₑ ∘ A.fₑ)) :
    (glue_Emb_of_Emb A B C D hᵥ hₑ hᵥ' hₑ').fₑ = (fun e => by
    match e with
    | Sum.inl e => exact C.fₑ e
    | Sum.inr e => exact D.fₑ e.val) := rfl

@[simp]

def glue_inter_Isom (A : G ⊆ᴳ H) (B : G ⊆ᴳ I) :
    G.Isom (inter (Emb1_glue A B).toHom (Emb2_glue A B).toHom) where
  fᵥ v := ⟨Sum.inl (A.fᵥ v), by
    simp only [Emb.glue, Set.mem_range, map, add_inc, Emb1_glue, Emb2_glue,
      Set.mem_inter_iff, Sum.inl.injEq, exists_eq, true_and]
    use B.fᵥ v
    simp only [Set.mem_range, exists_apply_eq_apply, ↓reduceDIte, Set.rangeSplitting_apply' B.fᵥinj]⟩
  fₑ e := ⟨Sum.inl (A.fₑ e), by
    simp only [Emb.glue, Set.mem_range, map, add_inc, Emb1_glue, Emb2_glue,
      Set.mem_inter_iff, Sum.inl.injEq, exists_eq, true_and]
    use B.fₑ e
    simp only [Set.mem_range, exists_apply_eq_apply, ↓reduceDIte, Set.rangeSplitting_apply' B.fₑinj]⟩
  inc e := by
    rw [subtype_eq, inter_inc_val]
    simp only [Emb.glue, map, Set.mem_range, add_inc, A.inc, Emb1_glue,
      Emb2_glue]
    repeat rw [← map_comp]
    congr
  fᵥinj v w h := by simpa only [Subtype.mk.injEq, Sum.inl.injEq, A.fᵥinj.eq_iff] using h
  fₑinj e f h := by simpa only [Subtype.mk.injEq, Sum.inl.injEq, A.fₑinj.eq_iff] using h
  fᵥsurj v := by
    obtain ⟨v', ⟨w, rfl⟩, u, hu⟩ := v
    simp only [Emb2_glue_fᵥ, Set.mem_range, Emb1_glue_fᵥ, Subtype.mk.injEq,
      Sum.inl.injEq] at hu ⊢
    split_ifs at hu with h
    case pos =>
      obtain ⟨v, rfl⟩ := h
      use v
      simpa [Set.rangeSplitting_apply' B.fᵥinj] using hu
  fₑsurj e := by
    obtain ⟨e', ⟨w, rfl⟩, u, hu⟩ := e
    simp only [Emb2_glue_fₑ, Set.mem_range, Emb1_glue_fₑ, Subtype.mk.injEq,
      Sum.inl.injEq] at hu ⊢
    split_ifs at hu with h
    case pos =>
      obtain ⟨e, rfl⟩ := h
      use e
      simpa [Set.rangeSplitting_apply' B.fₑinj] using hu


def inter_glue_Isom_union (A : G ⊆ᴳ I) (B : H ⊆ᴳ I) :
    (inter_Emb1 A B.toHom).glue (inter_Emb2 A.toHom B) ≃ᴳ union A.toHom B.toHom where
  fᵥ v := ⟨(A.add B.toHom).fᵥ (match v with
    | Sum.inl v => Sum.inl v
    | Sum.inr v => Sum.inr v.val),
    by simp only [bind_pure_comp, Set.mem_range, exists_apply_eq_apply]⟩
  fₑ e := ⟨(A.add B.toHom).fₑ (match e with
    | Sum.inl e => Sum.inl e
    | Sum.inr e => Sum.inr e.val),
    by simp only [bind_pure_comp, Set.mem_range, exists_apply_eq_apply]⟩
  inc e := by
    match e with
    | Sum.inl e =>
      simp only [Hom.add_fₑ_inl_apply, Emb.glue, map, inter_Emb2_fᵥ, Set.mem_range,
        Function.comp_apply, Subtype.exists, Set.mem_inter_iff, inter_Emb1_fᵥ, add_inc,
        subtype_eq, union_inc_val, A.inc]
      repeat rw [← map_comp]
      congr
    | Sum.inr e =>
      simp only [Hom.add_fₑ_inr_apply, Emb.glue, map, inter_Emb2_fᵥ, Set.mem_range,
        Function.comp_apply, Subtype.exists, Set.mem_inter_iff, inter_Emb1_fᵥ, add_inc,
        subtype_eq, union_inc_val, B.inc]
      repeat rw [← map_comp]
      congr
      ext w
      simp only [inter_Emb2_fᵥ, Set.mem_range, Function.comp_apply, Subtype.exists,
        Set.mem_inter_iff]
      split_ifs with hw
      case pos =>
        simp only [Hom.add_fᵥ_inl_apply, Set.apply_rangeSplitting, Subtype.impEmbedding_apply_coe]
        have : B.fᵥ w ∈ Set.range A.fᵥ ∩ Set.range B.fᵥ := by
          rw [mem_range_inter_Emb2_fᵥ] at hw
          simp_all only [Set.mem_range, Set.mem_inter_iff, exists_apply_eq_apply, and_self]
        rw [(by rfl : B.fᵥ w = ↑(⟨B.fᵥ w, this⟩: ↑(Set.range A.fᵥ ∩ Set.range B.fᵥ))),
          ← Subtype.ext_iff_val]
        apply_fun (inter_Emb2 A.toHom B).fᵥ using (inter_Emb2 A.toHom B).fᵥinj
        simp [Set.apply_rangeSplitting]
        apply_fun (Set.rangeFactorization B.fᵥ) using
          (Set.rangeFactorization_injective_iff B.fᵥ).mpr B.fᵥinj
        rw [Set.leftInverse_rangeSplitting B.fᵥ]
        rfl
      case neg =>
        rw [Hom.add_fᵥ_inr_apply]
  fᵥinj v w h := by
    simp only [Subtype.mk.injEq] at h
    match v, w with
    | Sum.inl v, Sum.inl w =>
      simp only [Hom.add_fᵥ_inl_apply, A.fᵥinj.eq_iff] at h
      rw [h]
    | Sum.inl v, Sum.inr w =>
      exfalso
      simp only [Hom.add_fᵥ_inl_apply, Hom.add_fᵥ_inr_apply, B.fᵥinj.eq_iff] at h
      obtain ⟨w, hw⟩ := w
      rw [Set.mem_compl_iff, mem_range_inter_Emb2_fᵥ] at hw
      simp only [Set.mem_range, not_exists] at hw h
      exact hw v h
    | Sum.inr v, Sum.inl w =>
      exfalso
      simp only [Hom.add_fᵥ_inl_apply, A.fᵥinj.eq_iff] at h
      obtain ⟨v, hv⟩ := v
      rw [Set.mem_compl_iff, mem_range_inter_Emb2_fᵥ] at hv
      simp only [Set.mem_range, not_exists, Hom.add_fᵥ_inr_apply] at hv h
      exact hv w h.symm
    | Sum.inr v, Sum.inr w =>
      simp only [Hom.add_fᵥ_inr_apply, B.fᵥinj.eq_iff] at h
      rwa [Sum.inr.injEq, Subtype.mk.injEq]
  fₑinj e f h := by
    simp only [bind_pure_comp, Subtype.mk.injEq] at h
    match e, f with
    | Sum.inl e, Sum.inl f =>
      simp only [Hom.add_fₑ_inl_apply, A.fₑinj.eq_iff] at h
      rw [h]
    | Sum.inl e, Sum.inr f =>
      exfalso
      simp only [Hom.add_fₑ_inl_apply, Hom.add_fₑ_inr_apply, A.fₑinj.eq_iff] at h
      obtain ⟨f, hf⟩ := f
      rw [Set.mem_compl_iff, mem_range_inter_Emb2_fₑ] at hf
      simp only [Set.mem_range, not_exists, Hom.add_fₑ_inr_apply] at hf h
      exact hf e h
    | Sum.inr e, Sum.inl f =>
      exfalso
      simp only [Hom.add_fₑ_inl_apply, Hom.add_fₑ_inr_apply, B.fₑinj.eq_iff] at h
      obtain ⟨e, he⟩ := e
      rw [Set.mem_compl_iff, mem_range_inter_Emb2_fₑ] at he
      simp only [Set.mem_range, not_exists, Hom.add_fₑ_inr_apply] at he h
      exact he f h.symm
    | Sum.inr e, Sum.inr f =>
      simp only [Hom.add_fₑ_inr_apply, B.fₑinj.eq_iff] at h
      rwa [Sum.inr.injEq, Subtype.mk.injEq]
  fᵥsurj v := by
    obtain ⟨u, vw, rfl⟩ := v
    simp only [Subtype.mk.injEq, Sum.exists, Hom.add_fᵥ_inl_apply, Hom.add_fᵥ_inr_apply,
      Subtype.exists, inter_Emb2_fᵥ, Set.mem_compl_iff, Set.mem_range, Function.comp_apply,
      Set.mem_inter_iff, not_exists, exists_prop]
    match vw with
    | Sum.inl v =>
      left
      use v
      rw [Hom.add_fᵥ_inl_apply]
    | Sum.inr w =>
      simp only [Hom.add_fᵥ_inr_apply, Set.rangeSplitting_eq_iff B.fᵥinj,
        Subtype.impEmbedding_apply_coe, and_imp, forall_exists_index, forall_apply_eq_imp_iff,
        B.fᵥinj.eq_iff, exists_eq_right, or_iff_not_imp_left, not_exists]
      tauto
  fₑsurj e := by
    obtain ⟨u, ew, rfl⟩ := e
    simp only [Subtype.mk.injEq, Sum.exists, Hom.add_fₑ_inl_apply, Hom.add_fₑ_inr_apply,
      Subtype.exists, inter_Emb2_fₑ, Set.mem_compl_iff, Set.mem_range, Function.comp_apply,
      Set.mem_inter_iff, not_exists, exists_prop]
    match ew with
    | Sum.inl e =>
      left
      use e
      rw [Hom.add_fₑ_inl_apply]
    | Sum.inr f =>
      simp only [Hom.add_fₑ_inr_apply, Set.rangeSplitting_eq_iff B.fₑinj,
        Subtype.impEmbedding_apply_coe, and_imp, forall_exists_index, forall_apply_eq_imp_iff,
        B.fₑinj.eq_iff, exists_eq_right, or_iff_not_imp_left, not_exists]
      tauto

end Graph
