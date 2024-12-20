import Kura

variable {V E : Type} [DecidableEq V] [DecidableEq E] (G : Graph V E)


/-
Ω is a cyclic permutation of a set Ωoverline.
This can be modeled as a list and application as sending to the next element in the list.

Let Ω|X be the restiction of Ω to the elements of X (i.e. Ω|X = Ω.filter (· ∈ X)).

For some list, L, of Ωoverline, it is clockwise if it is the same as Ω|L.

For v₁ v₂, let (Ω.cIco v₁ v₂) be the list of Ωoverline from v₁ to v₂.
Then (Ω.cIco v₁ v₂) and (Ω.cIco v₂ v₁) partition Ωoverline.
Let these kinds of bipartitions be fences of Ωoverline.

For v₁, v₂, v₃ and v₄, {v₁, v₂} crosses {v₃, v₄} if v₃ ∈ (Ω.cIco v₁ v₂) and v₄ ∈ (Ω.cIco v₂ v₁).

Society is a graph, G, with Ω defined on some subset of V(G).
Ω-Path is a path with its endpoints distinct and in Ωoverline.
For a set of vertex disjoint Ω-Paths, a fence for Ω is a fence for this set of paths if for all
Ω-Paths, P, it has one end in one side of the fence and the other end in the other side of the fence.
If there is a fence for a set of vertex disjoint Ω-Paths, then the set of paths is a transaction
in the society.

Given a transaction, T, a path, P, with its ends, a and b, is peripheral in T if (Ω.cIco a b) does
not contain any vertex of P' ∈ T \ {P} or (Ω.cIco b a) does not contain any vertex of P' ∈ T \ {P}.
A transaction with no peripheral paths is said to be crooked.

Let (G, Ω, Ω₀) be a neighborhood if G is a graph and Ω and Ω₀ are both cyclic permutations of
some subsets of V(G). Given a plane, Σ, a neighborhood is rural if G has a planar embedding Γ in Σ
without crossings and there are closed discs Δ₀ ⊆ Δ ⊆ Σ such that Γ does not use any point
outside Δ and inside Δ₀ and boundary(Δ₀) ∩ Γ = Ω₀overline with its orientation agreeing with Ω₀
and boundary(Δ) ∩ Γ = Ωoverline with its orientation agreeing with Ω.

A separation of a graph G is a pair of subgraphs (G₁, G₂) such that G = G₁ ∪ G₂ and E(G₁) ∩ E(G₂) =
∅. A separation of a society is a separation of G s.t. Ωoverline ⊆ V(G₂).
(G, Ω) is a composition of the society (G₁, Ω₁) with the neighborhood (G₂, Ω, Ω₁) if G₁ and G₂ are
a separation of G with Ω₁overline = V(G₁ ∩ G₂).
The sophistication of (G, Ω) is the minimum p ≥ 0 s.t. (G, Ω) is a composition of a society which
has no transactions of cardinality > p with a rural neighborhood.

-/

def Ω : List V := sorry
def Ω.cIcc (v₁ v₂ : V) : List V := sorry
def Ω.cIco (v₁ v₂ : V) : List V := sorry
def Ω.cIoc (v₁ v₂ : V) : List V := sorry
def Ω.cIoo (v₁ v₂ : V) : List V := sorry
structure Transaction where
  S : List G.Path
  a : V
  b : V
  ha : a ∈ Ω
  hb : b ∈ Ω
  hSdisj : ∀ P ∈ S, ∀ P' ∈ S, P ≠ P' → P.vertices ∩ P'.vertices = ∅
  hSfence : ∀ P ∈ S, P.start ∈ Ω.cIco a b ∧ P.finish ∈ Ω.cIoc a b

structure CrookedTransaction (G : Graph V E) extends Transaction G where
  hPcrooked : ∀ P ∈ S, ∀ P' ∈ S, P'.vertices ∩ Ω.cIco P.start P.finish = ∅ ∧
    P'.vertices ∩ Ω.cIco P.finish P.start = ∅

def sophistication (G : Graph V E) (Ω : List V) : ℕ := sorry

-- theorem thm2_1 (G : Graph V E) [simple G] (Z : Set V) (P : G.Path) (hP : Z ∩ P.vertices = ∅)
