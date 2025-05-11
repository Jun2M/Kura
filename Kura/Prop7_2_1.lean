import Kura.Operation.Minor2
import Kura.Operation.Simple


open Set Function
variable {α β α' α'' β' : Type*} {G G' H H' : Graph α β} {u v w : α} {e f : β} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set β} [Nonempty α] [Nonempty α'] [Nonempty β] [Nonempty β']
namespace Graph

theorem prop721_rec (t : ℕ) {G : Graph (Set α) (Sym2 (Set α))} [hV : Finite V(G)] [hE : Finite E(G)]
    [G.IsSimpleCanonical] (hVnonempty : V(G).Nonempty) (hGP : G.IsPartitionGraph)
    (hcard : 2^(t - 1) * V(G).ncard ≤ E(G).ncard) : G.HasCliqueMinor t := by
  have hEnonempty : E(G).Nonempty := by
    by_contra! hE
    simp only [hE, ncard_empty, nonpos_iff_eq_zero, mul_eq_zero, Nat.pow_eq_zero,
      OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at hcard
    have := hVnonempty.ncard_pos
    omega

  let e := hEnonempty.some
  obtain ⟨x, y, hxy : G.Inc₂ e x y⟩ := exists_inc₂_of_mem_edgeSet hEnonempty.some_mem
  have := prop721_rec t (G := G / ({e} : Set _) |>.Simplify)
  sorry

theorem prop721' (t : ℕ) {G : Graph (Set α) β} [G.IsSimple] [hV : Finite V(G)] [hE : Finite E(G)]
    (hVnonempty : V(G).Nonempty) (hGP : G.IsPartitionGraph) [Nonempty (Sym2 (Set α))] [Nonempty (Set α)]
    (hcard : 2^(t - 1) * V(G).ncard ≤ E(G).ncard) : G.HasCliqueMinor t := by
  revert G
  apply forall_Simplify
  rintro G _ _ _ hVnonempty hGP hcard
  exact prop721_rec t hVnonempty hGP hcard

theorem prop721 (t : ℕ) [hV : Finite V(G)] [hE : Finite E(G)] [G.IsSimple] (hVnonempty : V(G).Nonempty)
    (hcard : 2^(t - 1) * V(G).ncard ≤ E(G).ncard) : G.HasCliqueMinor t := by
  revert G
  apply forall_Setify
  rintro G hGP _ _ _ hVnonempty hcard
  exact prop721' t hVnonempty hGP hcard
