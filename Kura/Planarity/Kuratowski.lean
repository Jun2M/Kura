import Kura.Planarity.Euler
import Mathlib.Order.SymmDiff
import Kura.Dep.Toss


namespace Graph
open edge Sym2 symmDiff


lemma CompleteGraph5_not_Planar : IsEmpty <| Planar_by_AbstractDual (CompleteGraph 5) := by
  by_contra! h
  simp only [not_isEmpty_iff] at h
  obtain ⟨planar⟩ := h
  let G := CompleteGraph 5
  let l := Fintype.card G.Faces

  have h1 : l * 3 ≤ 2 * 10 := by
    refine (Nat.mul_le_mul_left l G.three_le_dualGraph_minDegree).trans ?_
    convert G.dualGraph.n_minDegree_le_two_m

  have hEuler : 5 + l - 10 = 2 := EulerFormula_of_connected G
  rw [Nat.sub_toss_eq' (by omega), Nat.toss_add_eq (by omega)] at hEuler
  rw [hEuler] at h1; clear hEuler
  omega


lemma CompleteBipGraph33_not_Planar : IsEmpty <| Planar_by_AbstractDual (CompleteBipGraph 3 3) := by
  by_contra! h
  simp only [not_isEmpty_iff] at h
  obtain ⟨planar⟩ := h
  let G := CompleteBipGraph 3 3
  let l := Fintype.card G.Faces

  have h1 : l * 4 ≤ 2 * 9 := by
    refine (Nat.mul_le_mul_left l G.four_le_dualGraph_minDegree_of_bipartite).trans ?_
    convert G.dualGraph.n_minDegree_le_two_m

  have hEuler : 6 + l - 9 = 2 := EulerFormula_of_connected G
  rw [Nat.sub_toss_eq' (by omega), Nat.toss_add_eq (by omega)] at hEuler
  rw [hEuler] at h1; clear hEuler
  omega

theorem KuraCore (n : ℕ) (hn : 1 < n) (Nx Ny : Finset (Fin n)) (hNxcard : Nx.card ≥ 2)
    (hNycard : Ny.card ≥ 2) :
    let G := ((CycleGraph n hn).addApex Nx).addApex (Sum.inl '' Ny ∪ {Sum.inr ()})
    IsEmpty ((CompleteGraph 5).MinorOf G) ∧ IsEmpty ((CompleteBipGraph 3 3).MinorOf G) →
    Nonempty (Planar_by_AbstractDual G) := by
  rintro G ⟨hK5, hK33⟩
  let y : G.Verts := Sum.inr ()
  let x : G.Verts := Sum.inl (Sum.inr ())
  let Ny' : Set G.Verts := Sum.inl '' (Sum.inl '' Ny)
  let Nx' : Set G.Verts := Sum.inl '' (Sum.inl '' Nx)

  let e : G.Edges := Sum.inr ⟨Sum.inr (), Set.mem_union_right (Sum.inl '' _) rfl⟩
  let G' := G.Es {e}ᶜ

  have hG' : ∃ S : Set G'.Verts, S.ncard = 2 ∧ G'.isCutBetween x y S := by
    by_cases hsymmdiff : Nx' ∆ Ny' = ∅
    · rw [← Set.bot_eq_empty, symmDiff_eq_bot] at hsymmdiff
      by_cases hNxcard2 : Nx'.ncard = 2
      · use Nx', hNxcard2, (by simp only [Set.mem_image, Sum.inl.injEq, exists_eq_right,
        reduceCtorEq, and_false, exists_false, not_false_eq_true, Nx', x]), (by simp only [
          Set.mem_image, reduceCtorEq, and_false, exists_const, not_false_eq_true, Nx', y])
        constructor
        · have hNxNonempty : Nx'.Nonempty := Set.nonempty_of_ncard_ne_zero (hNxcard2 ▸
            (Nat.zero_ne_add_one 1).symm)
          obtain ⟨v, hv⟩ := hNxNonempty
          exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (sorry : G'.adj x v)) (sorry : G'.adj v y)
        ·
          sorry
      · -- If there are at least 3 vertices mutually adjacent to x and y, then we can find a K5 minor
        absurd hK5
        simp only [not_isEmpty_iff]
        let l := ((List.finRange n).filter (· ∈ Nx)).take 3
        refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩⟩
        · intro v
          match v with
          | Sum.inl (Sum.inl v') =>
            by_cases h : v' ∈ Nx
            · exact some (l.indexOf v')
            · exact none
          | Sum.inl (Sum.inr v') => exact some 1
          | Sum.inr () => exact some 0
        · rintro ⟨e, he⟩
          let ⟨a, b⟩ := e.out
          sorry
        · sorry
        · sorry
        · sorry

    · wlog h : (Nx' \ Ny').Nonempty
      · specialize this n hn Ny Nx hNycard hNxcard
        -- needs commutativity between two addApex ops
        sorry

      obtain ⟨v, hv⟩ := h
      -- Find two nearest vertices to x in Ny
      -- split cycle into two parts
      sorry

  sorry


-- theorem KuraCore1 {V E : Type*} [LinearOrder V] [Fintype V] [LinearOrder E] [Fintype E]
--   (G : Graph V E) [Undirected G] {C : G.Cycle} {u v : V} (huNev : u ≠ v) (huNinC : u ∉ C.vertices)
--   (hvNinC : v ∉ C.vertices) (hV : C.vertices.toFinset ∪ {u, v} = Finset.univ)
--   (hud : 3 ≤ G.degree u) (hvd : 3 ≤ G.degree v) (huv : ∃ e : E, G.adj u v)
--   (hK5 : IsEmpty ((CompleteGraph 5).MinorOf G)) (hK33 : IsEmpty ((CompleteBipGraph 3 3).MinorOf G)):
--   ∃ (hP : Planar_by_AbstractDual G), G.FacialCycleOf C := by
--   let k : ℕ := C.vertices.length
--   let x : List V := C.vertices.filter (G.adj u)
--   have hxNeNil : x ≠ [] := sorry -- degree argument
--   let y : List V := C.vertices.filter (G.adj v)
--   have hyNeNil : y ≠ [] := sorry -- degree argument

--   have hK5Then : (x.inter y).length < 3 := by
--     by_contra! h
--     absurd hK5
--     let x1 : V := (x.inter y)[0]
--     let x2 : V := (x.inter y)[1]
--     let x3 : V := (x.inter y)[2]
--     let U : List V := [x1, x2, x3, u, v]
--     have hUNodup : U.Nodup := sorry -- huNinC, hvNinC and the fact that C is a cycle

--     simp only [not_isEmpty_iff]
--     sorry -- definition of minor needed



--   have huIn : u ∈ ({u, v} : Set V) := by simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
--     true_or]

--   -- let A : List ({u, v} : Set V) :=
--   --   let i : ℕ := C.vertices.indexOf (x.head hxNeNil)
--   --   let VL : List V := C.vertices.rotate i
--   --   let L : List ({u, v} : Set V) := G.RegionAssignment ⟨u, huIn⟩ VL
--   --   L.rotate (k - i)

--   have : ∃ (a b : V) (ha : a ∈ C.vertices) (hb : b ∈ C.vertices),
--       let ⟨P1, P2⟩ := C.split ha hb
--       ((P1.vertices.erase a).erase b).inter x = [] ∧
--       ((P2.vertices.erase a).erase b).inter y = [] := by
--     sorry -- Otherwise, we can find a K33 minor

--   obtain ⟨a, b, ha, hb, hP1P2⟩ := this
--   let ⟨P1, P2⟩ := C.split ha hb
--   simp only at hP1P2
--   obtain ⟨hP1, hP2⟩ := hP1P2

--   wlog hau : G.adj a u generalizing a u v E
--   · let G' := G.addUndirEdge s(a, u)
--     let C' := (SpanningSubgraphOf.addUndirEdge G s(a, u)).cycle C
--     have huNinC' : u ∉ C'.vertices := by
--       unfold C'; clear this
--       simp only [SubgraphOf.cycle_vertices, List.mem_map, not_exists, not_and]
--       rintro z hz

--       -- have h' := C'.vNodup' h ha
--       -- simp only [List.erase_cons_head, List.erase_cons_tail] at h'
--       -- exact h'.left
--       sorry
--     obtain hau' := this G' huNev.symm


--     sorry

--   sorry

-- theorem KuraCore2 {V E : Type*} [LinearOrder V] [Fintype V] [DecidableEq E] (G : Graph V E)
--   [Undirected G] [NConnected G 3] (hG5 : IsEmpty ((CompleteGraph 5).MinorOf G) )
--   (hG33 : IsEmpty ((CompleteBipGraph 3 3).MinorOf G)) : Nonempty (Planar_by_AbstractDual G) := by

--   sorry

-- Dual of (Gluing of G1 and G2) is Unlinegraph of (Clique sum of ((Line graph of (Dual of G1) and Line graph of (Dual of G2))))

theorem Kuratowski_AbstractDual {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] (G : Graph V E) [Undirected G] :
  Nonempty (Planar_by_AbstractDual G) ↔
  IsEmpty ((CompleteGraph 5).MinorOf G) ∧ IsEmpty ((CompleteBipGraph 3 3).MinorOf G) := by

  sorry
