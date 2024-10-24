import Kura.Conn.Tree
import Kura.Graph.Undirected

namespace Graph
open edge
variable {V₁ V₂ V₃ E₁ E₂ E₃ : Type*} [LinearOrder V₁] [LinearOrder V₂] [LinearOrder V₃]
  [LinearOrder E₁] [DecidableEq E₂] [DecidableEq E₃]
  {G : Graph V₁ E₁} [Undirected G]

def isTree (T : Graph V₁ E₂) : Prop := sorry

structure BranchDecomp (G : Graph V₁ E₁) where
  T : Graph V₂ E₂
  B : V₂ → Finset E₁
  isTree : T.isTree
  B_spec : sorry

def branchWidth (G : Graph V₁ E₁) [G.Undirected] : ℕ := sorry

structure Separation (G : Graph V₁ E₁) where
  EA : Set E₁

def Separation.EB (S : Separation G) : Set E₁ := S.EAᶜ

def Separation.A (S : Separation G) : Set V₁ :=
  { v | ∃ e ∈ S.EA, v = G.v1 e ∨ v = G.v2 e }

def Separation.B (S : Separation G) : Set V₁ :=
  { v | ∀ e ∈ S.EB, v = G.v1 e ∨ v = G.v2 e }

noncomputable def Separation.order (S : Separation G) : ℕ :=
  Nat.card (S.A ∩ S.B : Set V₁)

structure Tangle (G : Graph V₁ E₁) [G.Undirected] (k : ℕ) where
  isSmall : (S : Separation G) → (S.order < k) → Prop -- True if A is the small side
  notCover : ∀ (S₁ S₂ S₃ : Separation G), (hS₁ : S₁.order < k) → (hS₂ : S₂.order < k) →
    (hS₃ : S₃.order < k) → (isSmall S₁ hS₁) → (isSmall S₂ hS₂) → (isSmall S₃ hS₃) →
    S₁.EA ∪ S₂.EA ∪ S₃.EA ≠ Set.univ
  AneB : ∀ (S : Separation G), (S.order < k) → S.A ≠ S.B

def Tangle.indep (TT : Tangle G k) (X : Set V₁) : Prop := sorry

lemma k_le_branchWidth_of_tangle (G : Graph V₁ E₁) [G.Undirected] (k : ℕ) :
  Nonempty (Tangle G k) → k ≤ branchWidth G := sorry

-- Graph Minor X
lemma k_le_branchWidth_iff_tangle (G : Graph V₁ E₁) [G.Undirected] (k : ℕ) :
  k ≤ branchWidth G ↔ Nonempty (Tangle G k) := sorry

theorem Arb_tree_minor_of_A (G : Graph V₁ E₁) [G.Undirected] [Fintype V₂]
  (T : Graph V₂ E₂) (hT : T.isTree) (k : ℕ) (hk : Fintype.card V₂ ≤ k) (TT : Tangle G k) :
  ∃ (S : Separation G), S.order = k ∧ Tangle.indep TT (S.A ∩ S.B) ∧ T ≼ S.A := sorry



end Graph
