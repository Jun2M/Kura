import Kura.Planarity.Plainarity
import Kura.Dep.Toss


namespace Graph
open edge Sym2


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


-- private def RegionAssignment {V E : Type*} [LinearOrder V] [Fintype V] [LinearOrder E] [Fintype E]
--   (G : Graph V E) [Undirected G] {u v : V} : ({u, v} : Set V) → List V → List ({u, v} : Set V) :=
--   fun w L =>
--     let z := if w = u then v else u
--     let z' : ({u, v} : Set V) := ⟨z, by
--       unfold_let
--       split <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_or]⟩
--     match L with
--     | [] => []
--     | a :: as => if G.adj a z
--       then z' :: (G.RegionAssignment z' as)
--       else w :: (G.RegionAssignment w as)


theorem KuraCore1 {V E : Type*} [LinearOrder V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Graph V E) [Undirected G] {C : G.Cycle} {u v : V} (huNev : u ≠ v) (huNinC : u ∉ C.vertices)
  (hvNinC : v ∉ C.vertices) (hV : C.vertices.toFinset ∪ {u, v} = Finset.univ)
  (hud : 3 ≤ G.degree u) (hvd : 3 ≤ G.degree v) (huv : ∃ e : E, G.adj u v)
  (hK5 : IsEmpty ((CompleteGraph 5).MinorOf G)) (hK33 : IsEmpty ((CompleteBipGraph 3 3).MinorOf G)):
  ∃ (hP : Planar_by_AbstractDual G), G.FacialCycleOf C := by
  let k : ℕ := C.vertices.length
  let x : List V := C.vertices.filter (G.adj u)
  have hxNeNil : x ≠ [] := sorry -- degree argument
  let y : List V := C.vertices.filter (G.adj v)
  have hyNeNil : y ≠ [] := sorry -- degree argument

  have hK5Then : (x.inter y).length < 3 := by
    by_contra! h
    absurd hK5
    let x1 : V := (x.inter y)[0]
    let x2 : V := (x.inter y)[1]
    let x3 : V := (x.inter y)[2]
    let U : List V := [x1, x2, x3, u, v]
    have hUNodup : U.Nodup := sorry -- huNinC, hvNinC and the fact that C is a cycle

    simp only [not_isEmpty_iff]
    sorry -- definition of minor needed



  have huIn : u ∈ ({u, v} : Set V) := by simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
    true_or]

  -- let A : List ({u, v} : Set V) :=
  --   let i : ℕ := C.vertices.indexOf (x.head hxNeNil)
  --   let VL : List V := C.vertices.rotate i
  --   let L : List ({u, v} : Set V) := G.RegionAssignment ⟨u, huIn⟩ VL
  --   L.rotate (k - i)

  have : ∃ (a b : V) (ha : a ∈ C.vertices) (hb : b ∈ C.vertices),
      let ⟨P1, P2⟩ := C.split ha hb
      ((P1.vertices.erase a).erase b).inter x = [] ∧
      ((P2.vertices.erase a).erase b).inter y = [] := by
    sorry -- Otherwise, we can find a K33 minor

  obtain ⟨a, b, ha, hb, hP1P2⟩ := this
  let ⟨P1, P2⟩ := C.split ha hb
  simp only at hP1P2
  obtain ⟨hP1, hP2⟩ := hP1P2

  wlog hau : G.adj a u generalizing a u E
  · let G' := G.addUndirEdge s(a, u)
    obtain hau' := this G'


    sorry

  sorry

-- theorem KuraCore2 {V E : Type*} [LinearOrder V] [Fintype V] [DecidableEq E] (G : Graph V E)
--   [Undirected G] [NConnected G 3] (hG5 : IsEmpty ((CompleteGraph 5).MinorOf G) )
--   (hG33 : IsEmpty ((CompleteBipGraph 3 3).MinorOf G)) : Nonempty (Planar_by_AbstractDual G) := by

--   sorry

-- Dual of (Gluing of G1 and G2) is Unlinegraph of (Clique sum of ((Line graph of (Dual of G1) and Line graph of (Dual of G2))))

-- theorem Kuratowski_AbstractDual {V E : Type*} [LinearOrder V] [Fintype V] (G : Graph V E) [Undirected G] :
--   Planar_by_AbstractDual G ↔ ¬ G.hasMinor (CompleteGraph 5) ∧ ¬ G.hasMinor (CompleteBipGraph 3 3) := by

  -- sorry
