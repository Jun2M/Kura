import Kura
import Kura.Dep.Toss

namespace Graph
open edge Sym2
variable {α V W E F : Type*} {G : Graph V E} {H : Graph W F} [Simple G] [Simple H]


def ColorSubgraph (c : F → α) (hGH : G ⊆ᴳ H) (a : α) : Prop :=
  ∀ e₁ e₂ : E, c (hGH.fₑ e₁) = a ∧ c (hGH.fₑ e₂) = a

def MonoChromeSubgraph (c : F → α) (hGH : G ⊆ᴳ H) : Prop :=
  ∃ a : α, ColorSubgraph c hGH a

lemma R33 (c : _ → Fin 2) : ∃ (hGH : (CompleteGraph 3) ⊆ᴳ (CompleteGraph 6)),
  MonoChromeSubgraph c hGH := by
  sorry

instance instexistMonoChromeSubgraphDec [Fintype V] [Fintype W] (c : F → Fin 2) (k : Fin 2) :
    Decidable (∃ (hGH : G ⊆ᴳ H), ColorSubgraph c hGH k) := by
  sorry

lemma exists_ramsey_number (s t : ℕ) :
    ∃ (n : ℕ), ∀ (c : Fin (Nat.choose n 2) → Fin 2),
    ( (∃ (hGH : CompleteGraph s ⊆ᴳ CompleteGraph n), ColorSubgraph c hGH 0) ∨
      (∃ (hGH : CompleteGraph t ⊆ᴳ CompleteGraph n), ColorSubgraph c hGH 1) ) := by
  sorry

def RamseyNumber (s t : ℕ) := Nat.find (exists_ramsey_number s t)

lemma RamseyNumber_symm (s t : ℕ) : RamseyNumber s t = RamseyNumber t s := by
  unfold RamseyNumber
  congr
  ext n
  simp only [Fin.isValue, eq_iff_iff]
  constructor <;>
  · intro h c
    obtain ⟨hGH, h⟩ | ⟨hGH, h⟩ := h (c · +1)
    · right
      use hGH
      intro e₁ e₂
      obtain ⟨h₁, h₂⟩ := h e₁ e₂
      rw [add_toss_eq] at h₁ h₂
      rw [h₁, h₂]
      refine ⟨rfl, by rfl⟩
    · left
      use hGH
      intro e₁ e₂
      obtain ⟨h₁, h₂⟩ := h e₁ e₂
      rw [add_toss_eq] at h₁ h₂
      rw [h₁, h₂]
      refine ⟨by rfl, rfl⟩

lemma RamseyNumber_two (s : ℕ) (hs : 2 ≤ s) : RamseyNumber s 2 = s := by
  unfold RamseyNumber
  rw [Nat.find_eq_iff]
  constructor
  · intro c
    by_cases h : ∃ hGH : (CompleteGraph 2).SubgraphOf (CompleteGraph s), ColorSubgraph c hGH 1
    · right
      exact h
    · simp at h
      left
      use SubgraphOf.refl _
      intro e₁ e₂
      simp only [SubgraphOf.refl_fₑ, Function.Embedding.refl_apply, Fin.isValue]
      sorry
  · intro n hn
    simp only [Fin.isValue, not_forall, not_or, not_exists]
    use fun _ => 0
    constructor
    · intro h
      exfalso
      sorry
    · intro h
      simp only [ColorSubgraph, Fin.isValue, zero_ne_one, and_self, Nat.choose_self, forall_const,
        not_false_eq_true]

lemma RamseyNumber_le_prev_add_prev (s t : ℕ) (hs : 3 ≤ s) (ht : 3 ≤ t) :
    RamseyNumber s t ≤ RamseyNumber (s - 1) t + RamseyNumber s (t - 1) := by
  let n := RamseyNumber (s -1) t + RamseyNumber s (t - 1)
  have : NeZero n := sorry
  change RamseyNumber s t ≤ n
  unfold RamseyNumber
  rw [Nat.find_le_iff]
  use n, (by rfl)
  intro c
  let v : Fin n := 0
  let d0v := ((CompleteGraph n).outEdges v).filter (c · = 0)
  let N0v := d0v.image (λ e => (CompleteGraph n).goFrom (v := v) (e := e) sorry)
  let d1v := ((CompleteGraph n).outEdges v).filter (c · = 1)
  have h : RamseyNumber (s-1) t ≤ d0v.card ∨ RamseyNumber s (t-1) ≤ d1v.card := sorry
  rcases h with h | h
  unfold RamseyNumber at h
  simp at h
  obtain ⟨m, hm, h⟩ := h
  let c' : Fin (m.choose 2) → Fin 2 := sorry -- backmap of c to neighborhood of v
  specialize h c'
  obtain ⟨hGH, h⟩ | ⟨hGH, h⟩ := h
  · left
    sorry
    -- ColorSubgraph c (hGH.trans (Vs_subgraph _ _)) 1
  · right
    -- use hGH.trans ((CompleteGraph n).Vs_subgraph ↑N0v)

    sorry
  sorry

def DiagRamseyNumber (s) := RamseyNumber s s

lemma DiagRamseyNumber_le_two_pow (s : ℕ) : DiagRamseyNumber s ≤ 2 ^ (2 * s - 2) := by sorry

-- Erdős
theorem ProbablisticLowerBoundOfDiagRamseyNumber (s n : ℕ) (hs : 2 ≤ s)
  (hn : n.choose s * 2 ^ (1 - s.choose 2) < 1) : n < DiagRamseyNumber s := by
  let Ω : List (E → Fin 2) := Finset.univ.Sort
  have hΩ : Ω.length = 2 ^ n.choose 2 := by sorry
  have hT : ∀ T : Finset (Fin n), T.card = s →
    (Ω.filter (λ c => ColorSubgraph (CompleteGraph n)[T.toSet]ᴳ c 0)).length =
    2 ^ ( n.choose 2 - s.choose 2 ) := by sorry
  have hT' : Finset.univ.finsetcard s = n.choose s := by sorry
  have hT0 : Ω.filter (λ c => ∃ (T : Finset (Fin n)), T.card = s ∧
    ColorSubgraph (CompleteGraph n)[T.toSet]ᴳ c 0).length =
    n.choose s * 2 ^ ( n.choose 2 - s.choose 2 ) := by sorry
  -- similarly for 1

  have hΩ : Ω.filter (λ c => ¬ (∃ (T : Finset (Fin n)), T.card = s ∧
    ColorSubgraph (CompleteGraph n)[T.toSet]ᴳ c 0)).length =
    2 ^ n.choose 2 - n.choose s * 2 ^ ( n.choose 2 - s.choose 2 ) := by sorry
  have harith : 2 ^ n.choose 2 - n.choose s * 2 ^ ( n.choose 2 - s.choose 2 ) > 0 := by sorry
  sorry

lemma cor (s : ℕ) (hs : 3 ≤ s) : 2 ^ (s / 2) < DiagRamseyNumber s := by
  let n := ⌊2 ^ (s / 2)⌋
  have since : n.choose 2 < n ^ s / s.factorial := by sorry
  have also : s ^ (1 - s.choose 2) = s ^ (1 + s / 2) / s ^ (s^2 /2) := by sorry
  have arith :=
    calc n.choose s * 2 ^ (1 - s.choose 2) ≤ n^2 / s.factorial * 2 ^ (1 + s / 2) / s ^ (s^2 /2)
                                           ≤ 2 ^ (1 + s / 2) / s.factorial
                                           < 1 := by sorry

lemma exist_multicolorRamsey (k : ℕ) (s : Fin k → ℕ) (hk : 3 ≤ k) (hs : ∀ i, 2 ≤ s i) :
    ∃ (n : ℕ), ∀ (c : Fin (n.choose 2) → Fin k),
    (∀ i : Fin k, ∃ (hGH : CompleteGraph (s i) ⊆ᴳ CompleteGraph n), ColorSubgraph c hGH i) := by
  use MultiColorRamseyNumber (k - 1) (if i = Fin.last _ then RamseyNumber (s (Fin.last _ - 1)) (s (Fin.last _)) else s i)
  intro c
  by_contra h : ∀ i, ∀ hGH : CompleteGraph (s i) ⊆ᴳ CompleteGraph (MultiColorRamseyNumber (k - 1) (if i = Fin.last _ then RamseyNumber (s (Fin.last _ - 1)) (s (Fin.last _)) else s i)), ¬ ColorSubgraph c hGH i
  merge last two colors
  Then there exist a "monochrome" Kₜ where t ≥ RamseyNumber (s (Fin.last _ - 1)) (s (Fin.last _))
  This graph must contain a monochrome complete of color either last or second last
  sorry

def MultiColorRamseyNumber (k : ℕ) (s : Fin k → ℕ) := @Nat.find (λ n => ∀ c : (Fin $ n.choose 2) → Fin k,
  ∃ i : Fin k, ∃ (hGH : CompleteGraph (s i) ⊆ᴳ CompleteGraph n), ColorSubgraph c hGH i) sorry

def generalRamsey (G : Graph V E) (H : Graph W F) := @Nat.find (λ n => ∀ c : (Fin $ n.choose 2) → Fin 2,
  (∃ (hGH : G ⊆ᴳ CompleteGraph n), ColorSubgraph c hGH 0) ∨
  (∃ (hGH : H ⊆ᴳ CompleteGraph n), ColorSubgraph c hGH 1)) sorry
  -- Find the complete graphs that contains G and H respectively, Find thier Ramsey number, that is an upper bound hence exists

theorem upperBoundOnGeneralRamsey [Connected H] (hW : Fintype.card W = n) : (chromaticNumber G -1) * (n - 1) < generalRamsey G H := by
  let m := (chromaticNumber G -1) * (n - 1)
  -- let Vs : Fin (chromaticNumber G - 1) → Set (Fin m) := sorry -- s.t. Vs partitions Fin m with sets of size n - 1
  let P : Fin m → Fin (chromaticNumber G - 1) := sorry -- s.t. P is a coloring
  let c : Fin (n.choose 2) → Fin 2 := fun e => if P ((CompleteGraph m).v1 e) ≠ P ((CompleteGraph m).v2 e) then 1 else 0
  have : ¬ (∃ (hGH : H ⊆ᴳ CompleteGraph n), ColorSubgraph c hGH 1) := by sorry -- doesn't fit in any of n-1 size connected components
  have : ¬ (∃ (hGH : G ⊆ᴳ CompleteGraph n), ColorSubgraph c hGH 0) := by sorry -- use P as a vertex coloring of G that would contradict chromatic number
  sorry

-- Chvátal
theorem Chvatal (n m : ℕ) (T : TreeGraph m) : (generalRamsey T (CompleteGraph n) : ℕ) = (m - 1) * (n - 1) +1 := by
  apply le_antisymm
  · -- use upperBoundOnGeneralRamsey
    sorry
  · let M := (m - 1) * (n - 1) +1
    induction m using Nat.strongInductionOn generalizing T
    induction n using Nat.strongInductionOn generalizing T
    let x : Fin m := sorry -- leaf of T
    let y : Fin m := sorry -- parent of x
    let T' := T.removeEdge (T.edge x y)
    obtain ⟨c, hc1 | hc2⟩ := IH n m T' sorry
    -- hc1 : (∃ (hGH : T' ⊆ᴳ CompleteGraph M), ColorSubgraph c hGH 0)
    -- hc2 : (∃ (hGH : CompleteGraph n ⊆ᴳ CompleteGraph M), ColorSubgraph c hGH 1)
    · let K := CompleteGraph M - T'
      have hK : |V(K)| = M - (m - 1) = (m - 1) * (n - 2) + 1 := by sorry
      obtain ⟨c', hc'1 | hc'2⟩ := IH (n - 1) m T
      -- hc'1 : (∃ (hGH : T ⊆ᴳ CompleteGraph K), ColorSubgraph c' hGH 0)
      -- hc'2 : (∃ (hGH : CompleteGraph (n - 1) ⊆ᴳ CompleteGraph K), ColorSubgraph c' hGH 1)
      · sorry -- done
      · -- If there exist an edge between y and vertices in CompleteGraph (n - 1)
        -- then extend T' by this edge to get monochrome T in CompleteGraph M
        -- else extend CompleteGraph (n - 1) by y to get monochrome CompleteGraph n
        sorry
    · sorry -- done

-- Constructive bound for DiagRamseyNumber?
-- Frank & Wilson 1981
theorem FrankWilson (k : ℕ) (𝓕 : Fin m → Set (Fin n)) (h𝓕 : ∀ i, |𝓕 i| = k) [Prime p]
  (M : Fin s ↪ ZMod p) (hk : k = M 0) (H : {M i | i ≠ 0} = { |𝓕 l ∩ 𝓕 j| | l ≠ j }) :
  m = n.choose s := by sorry

end Graph
