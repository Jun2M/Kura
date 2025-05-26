import Kura.Operation.Minor2Simp


open Set Function
variable {α β α' α'' β' : Type*} {G G' H H' : Graph α β} {u v w : α} {e f : β} {x y z : α'}
  {S S' T T' U U': Set α} {F F' R R' : Set β}
namespace Graph

theorem prop721_rec (t : ℕ) [Nonempty α] {G : Graph (Set α) (Sym2 (Set α))}
    [hV : Finite V(G)] [hE : Finite E(G)] [G.SimpleCanonical] (hVnonempty : V(G).Nonempty)
    (hGP : G.IsPartitionGraph) (hcard : 2^(t - 1) * V(G).ncard ≤ E(G).ncard) : G.HasCliqueMinor t := by
  have hEnonempty : E(G).Nonempty := by
    by_contra! hE
    simp only [hE, ncard_empty, nonpos_iff_eq_zero, mul_eq_zero, Nat.pow_eq_zero,
      OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at hcard
    have := hVnonempty.ncard_pos
    omega

  let e := hEnonempty.some
  obtain ⟨x, y, hxy : G.IsLink e x y⟩ := exists_isLink_of_mem_edgeSet hEnonempty.some_mem
  have : E(G // (Set.singleton e)).ncard < E(G).ncard := by
    have he_mem_E : e ∈ E(G) := hEnonempty.some_mem
    let G_contracted := G / (Set.singleton e)
    have h_contract : E(G_contracted).ncard < E(G).ncard := by
      exact setContract_edgeSet_ncard_lt_singleton_iff G e |>.mpr he_mem_E
    have h_simplify_le : E(G_contracted.simplify).ncard ≤ E(G_contracted).ncard := by
      apply simplify_edgeSet_ncard_le
    exact Nat.lt_of_le_of_lt h_simplify_le h_contract

  simp at this
  have h_V_G_prime_nonempty : V(G // (Set.singleton e)).Nonempty := by
    simp only [SimpMinor, simplify_vertexSet, setContract_vertexSet]
    exact hVnonempty.image (⋃₀ (G ↾ Set.singleton e).Component · )

  have h_G_prime_IsPartitionGraph : (G // (Set.singleton e)).IsPartitionGraph := by
    simp only [SimpMinor]
    have hGP_c := SetContract.IsPartitionGraph (Set.singleton e) hGP
    obtain ⟨P_val, hP_eq⟩ := hGP_c
    use P_val
    simp only [simplify_vertexSet, hP_eq]

  have h_card_G_prime : 2^(t - 1) * V(G // (Set.singleton e)).ncard ≤ E(G // (Set.singleton e)).ncard := by
    sorry

  let G_prime := G // (Set.singleton e)
  have h_recursive_call : G_prime.HasCliqueMinor t :=
    prop721_rec t h_V_G_prime_nonempty h_G_prime_IsPartitionGraph h_card_G_prime

  sorry

termination_by E(G).ncard
decreasing_by exact this

theorem prop721 (t : ℕ) [G.Simple] [hV : Finite V(G)] [hE : Finite E(G)] (hVnonempty : V(G).Nonempty)
    (hcard : 2^(t - 1) * V(G).ncard ≤ E(G).ncard) : G.HasCliqueMinor t := by
  revert G
  apply forall_type_nonempty
  intro α β hα hβ
  apply forall_setify
  intro G h hS
  revert h
  apply forall_Simplify |₂ (fun {β} G ↦ ∀ [hS : G.Simple], G.IsPartitionGraph → ∀ [hV : Finite ↑V(G)]
    [hE : Finite ↑E(G)], V(G).Nonempty → 2 ^ (t - 1) * V(G).ncard ≤ E(G).ncard → G.HasCliqueMinor t)
  intro G _ _ hGP _ _ hVnonempty hcard
  exact prop721_rec t hVnonempty hGP hcard
