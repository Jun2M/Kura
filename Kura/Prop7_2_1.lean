import Kura.Operation.Minor2
import Kura.Operation.Simple


open Set Function
variable {α ε α' α'' ε' : Type*} {G G' H H' : Graph α ε} {u v w : α} {e f : ε} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set ε} [Nonempty α] [Nonempty α'] [Nonempty ε] [Nonempty ε']
namespace Graph

theorem prop721_rec (t : ℕ) {G : Graph (Set α) (Sym2 (Set α))} [hV : Finite G.V] [hE : Finite G.E]
    [G.IsSimpleCanonical] (hVnonempty : G.V.Nonempty) (hGP : G.IsPartitionGraph)
    (hcard : 2^(t - 1) * G.V.ncard ≤ G.E.ncard) : G.HasCliqueMinor t := by
  have hEnonempty : G.E.Nonempty := by
    by_contra! hE
    simp only [hE, ncard_empty, nonpos_iff_eq_zero, mul_eq_zero, Nat.pow_eq_zero,
      OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at hcard
    have := hVnonempty.ncard_pos
    omega

  let e := hEnonempty.some
  obtain ⟨x, y, hxy : G.Inc₂ e x y⟩ := exists_inc₂_of_mem_edgeSet hEnonempty.some_mem
  let G' := G / ({e} : Set _) |>.Simplify
  -- have := prop721' t (G := G')
  sorry

theorem prop721' (t : ℕ) {G : Graph (Set α) ε} [G.IsSimple] [hV : Finite G.V] [hE : Finite G.E]
    (hVnonempty : G.V.Nonempty) (hGP : G.IsPartitionGraph) [Nonempty (Set α)] [Nonempty (Sym2 (Set α))]
    (hcard : 2^(t - 1) * G.V.ncard ≤ G.E.ncard) : G.HasCliqueMinor t := by
  have hisom := simplify_isom (G := G)
  have := @prop721_rec _ _ t (G := Simplify G) hV ?_ _ hVnonempty hGP ?_
  exact hisom.HasCliqueMinor (α := Set α) (α' := Set α) (ε := ε) (ε' := Sym2 (Set α)) 



theorem prop721 (t : ℕ) [hV : Finite G.V] [hE : Finite G.E] [G.IsSimple] (hVnonempty : G.V.Nonempty)
    (hcard : 2^(t - 1) * G.V.ncard ≤ G.E.ncard) : G.HasCliqueMinor t := by
  revert G
  apply forall_Setify
  rintro G hGP _ _ _ hVnonempty hcard
  exact prop721' t hVnonempty hGP hcard
