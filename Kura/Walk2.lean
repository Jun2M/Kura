import Kura.Subgraph
import Kura.Minor
import Mathlib.Data.Finset.Lattice.Basic
import Kura.Dep.List

open Set Function List Nat
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e f g : β}
namespace Graph


inductive Walk (α β : Type*) where
| nil (u : α) : Walk α β
| cons (u : α) (e : β) (W : Walk α β) : Walk α β

namespace Walk
variable {w w₁ : Walk α β} {w₂ : Walk α β}

def ValidOn (w : Walk α β) (G : Graph α β) (u v : α) : Prop :=
  match w with
  | nil x => x = u ∧ x = v ∧ x ∈ G.V
  | cons x e (nil y) => x = u ∧ y = v ∧ G.IsBetween e x y
  | cons x e (cons y f w) => x = u ∧ G.IsBetween e x y ∧ ValidOn (cons y f w) G y v

def vx : Walk α β → List α
| nil x => [x]
| cons x _e w => x :: w.vx

instance : Membership α (Walk α β) where
  mem w x := x ∈ w.vx

instance [DecidableEq α] : Decidable (x ∈ w) := by
  change Decidable (x ∈ w.vx)
  infer_instance

def edge : Walk α β → List β
| nil _ => []
| cons _ e w => e :: w.edge

def length : Walk α β → ℕ
| nil _ => 0
| cons _ _ w => w.length + 1

def concat : Walk α β → β → α → Walk α β
| nil x, e, y => cons x e (nil y)
| cons x e w, f, y => cons x e (w.concat f y)

def append : Walk α β → Walk α β → Walk α β
| nil _x, w => w
| cons x e w, w' => cons x e (w.append w')

def reverse : Walk α β → Walk α β
| nil x => nil x
| cons x e w => w.reverse.concat e x

def startAt [DecidableEq α] (w : Walk α β) (u : α) (h : u ∈ w) : Walk α β :=
  match w with
  | nil x => nil x
  | cons x e w =>
    if hin : u ∈ w
    then startAt w u hin
    else cons x e w

@[simp]
lemma cons_length : (cons x e w).length = w.length + 1 := rfl


lemma startAt_length_le [DecidableEq α] {w : Walk α β} (h : u ∈ w) : (startAt w u h).length ≤ w.length := by
  match w with
  | nil x => simp [startAt]
  | cons x e w =>
    simp only [startAt, cons_length]
    split_ifs with hin
    · have := startAt_length_le hin
      omega
    · simp

/-- Removes duplicate vertices from a walk, keeping only the first occurrence of each vertex. -/
def dedup [DecidableEq α] : Walk α β → Walk α β
| nil x => nil x
| cons x e w =>
  if h : x ∈ w
  then by
    have := startAt_length_le h
    exact (startAt w x h).dedup
  else cons x e (dedup w)
termination_by w => w.length

@[simp] lemma nil_vx : (nil x : Walk α β).vx = [x] := rfl

@[simp] lemma nil_edge : (nil x : Walk α β).edge = [] := rfl

@[simp] lemma nil_length : (nil x : Walk α β).length = 0 := rfl

@[simp] lemma nil_validOn (hx : x ∈ G.V) : (nil x : Walk α β).ValidOn G x x := by
  simp [ValidOn, hx]

@[simp] lemma cons_vx : (cons x e w).vx = x :: w.vx := rfl

@[simp] lemma cons_edge : (cons x e w).edge = e :: w.edge := rfl

lemma ValidOn.eq_left (h : (cons x e w).ValidOn G u v) : u = x := by
  match w with
  | nil y =>
    obtain ⟨rfl, rfl, hu⟩ := h
    simp
  | cons y f w' =>
    obtain ⟨rfl, h⟩ := h
    simp

@[simp] lemma cons_validOn (hw : w.ValidOn G y z) (he : G.IsBetween e x y) :
  (cons x e w).ValidOn G x z := by
  match w with
  | nil u =>
    obtain ⟨rfl, rfl, hu⟩ := hw
    refine ⟨rfl, rfl, he⟩
  | cons u f w' =>
    obtain rfl := hw.eq_left
    refine ⟨rfl, he, hw⟩

end Walk

open Walk

variable {G H : Graph α β} {u v : α} {e : β} {w : Walk α β}

def IsBetween.Walk (_h : G.IsBetween e u v) : Walk α β := cons u e (nil v)

lemma IsBetween.walk_validOn (h : G.IsBetween e u v) : h.Walk.ValidOn G u v := by
  simp [Walk, ValidOn, h]

@[simp] lemma IsBetween.Walk.vx (h : G.IsBetween e u v): h.Walk.vx = [u, v] := rfl

@[simp] lemma IsBetween.Walk.edge (h : G.IsBetween e u v): h.Walk.edge = [e] := rfl

@[simp] lemma IsBetween.Walk.length (h : G.IsBetween e u v): h.Walk.length = 1 := rfl

/-- Given a graph adjacency, we can create a walk of length 1 -/
lemma Adj.exist_walk (h : G.Adj u v) : ∃ (W : Walk α β), W.ValidOn G u v ∧ W.length = 1 := by
  obtain ⟨e, he⟩ := h
  use he.Walk, he.walk_validOn
  rfl

/-- Given a reflexive adjacency, we can create a walk of length at most 1 -/
lemma reflAdj.exist_walk (h : G.reflAdj u v) : ∃ (W : Walk α β), W.ValidOn G u v ∧ W.length ≤ 1 := by
  obtain hadj | ⟨rfl, hx⟩ := h
  · obtain ⟨W, hW, hlength⟩ := hadj.exist_walk
    use W, hW
    rw [hlength]
  · use nil u
    constructor
    · simp [ValidOn, hx]
    · simp

namespace Walk

lemma vx_ne_nil {w : Walk α β} : w.vx ≠ [] := by
  match w with
  | nil x => simp
  | cons x e w => simp

/-- Properties of append operation -/
@[simp]
lemma append_vx {w₁ w₂ : Walk α β} : (append w₁ w₂).vx = w₁.vx.dropLast ++ w₂.vx := by
  induction w₁ with
  | nil x => simp [append]
  | cons x e w ih =>
    simp only [append, cons_vx, ih]
    rw [List.dropLast_cons_of_ne_nil vx_ne_nil]
    simp

@[simp]
lemma append_edge {w₁ w₂ : Walk α β} : (append w₁ w₂).edge = w₁.edge ++ w₂.edge := by
  induction w₁ with
  | nil x => simp [append]
  | cons x e w ih =>
    simp [append, ih]

@[simp]
lemma append_length {w₁ w₂ : Walk α β} : (append w₁ w₂).length = w₁.length + w₂.length := by
  induction w₁ with
  | nil x => simp [append]
  | cons x e w ih =>
    simp only [append, cons_length, ih]
    omega

/-- Properties of concat operation -/
@[simp]
lemma concat_vx {w : Walk α β} {e : β} {v : α} : (w.concat e v).vx = w.vx ++ [v] := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_edge {w : Walk α β} {e : β} {v : α} : (w.concat e v).edge = w.edge ++ [e] := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_length {w : Walk α β} {e : β} {v : α} : (w.concat e v).length = w.length + 1 := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

/-- Properties of reverse operation -/
@[simp]
lemma reverse_vx {w : Walk α β} : (reverse w).vx = w.vx.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_edge {w : Walk α β} : (reverse w).edge = w.edge.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_length {w : Walk α β} : (reverse w).length = w.length := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

-- /-- Properties of dedup operation -/
-- lemma dedup_validOn [DecidableEq α] {w : Walk α β} (h : w.ValidOn G u v) : (dedup w).ValidOn G u v := sorry

-- lemma dedup_vx_nodup [DecidableEq α] (w : Walk α β) : (dedup w).vx.Nodup := sorry

-- /-- If there's a valid walk from u to v in graph G, then u and v are connected in G -/
-- lemma connected_of_validOn (h : w.ValidOn G u v) : G.Connected u v := sorry

-- lemma validOn_of_append (h₁ : w₁.ValidOn G u v) (h₂ : w₂.ValidOn G v z) :
--   (append w₁ w₂).ValidOn G u z := sorry

-- lemma validOn_of_concat (h : w.ValidOn G u v) (hbtw : G.IsBetween e v z) :
--   (w.concat e z).ValidOn G u z := sorry

-- lemma validOn_of_reverse (h : w.ValidOn G u v) : (reverse w).ValidOn G v u := sorry

-- /-- If the endpoints of a walk are connected in G, there exists a valid walk between them -/
-- lemma validOn_of_connected (h : G.Connected u v) : ∃ w : Walk α β, w.ValidOn G u v := sorry

-- /-- Two vertices are connected in a graph if and only if there exists a valid walk between them -/
-- @[simp]
-- lemma connected_iff_exists_validOn : G.Connected u v ↔ ∃ w : Walk α β, w.ValidOn G u v :=
--   ⟨validOn_of_connected, fun ⟨w', h⟩ => connected_of_validOn h⟩

/-- A subgraph inherits all valid walks -/
lemma ValidOn.le {w : Walk α β} {u v : α} (h : w.ValidOn G u v) (hle : G ≤ H) : w.ValidOn H u v := by
  match w with
  | nil x =>
    obtain ⟨rfl, rfl, hx⟩ := h
    use rfl, rfl, mem_of_le hle hx
  | cons x e (nil y) =>
    obtain ⟨rfl, rfl, hx⟩ := h
    exact ⟨rfl, rfl, hx.le hle⟩
  | cons x e (cons y f w) =>
    obtain ⟨rfl, hbtw, hvalid⟩ := h
    exact ⟨rfl, hbtw.le hle, hvalid.le hle⟩

lemma ValidOn.mem_of_mem_vx {w : Walk α β} {u v : α} (h : w.ValidOn G u v) (hmem : x ∈ w.vx) :
    x ∈ G.V := by
  match w with
  | nil x =>
    convert h.2.2
    simpa using hmem
  | cons x e (nil y) =>
    obtain ⟨rfl, rfl, hx⟩ := h
    simp only [cons_vx, nil_vx, mem_cons, not_mem_nil, or_false] at hmem
    obtain rfl | rfl := hmem
    · exact hx.vx_mem_left
    · exact hx.vx_mem_right
  | cons x e (cons y f w) =>
    obtain ⟨rfl, hbtw, hvalid⟩ := h
    rw [cons_vx, List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · exact hbtw.vx_mem_left
    · exact hvalid.mem_of_mem_vx hmem

lemma ValidOn.mem_of_mem_edge {w : Walk α β} {u v : α} (h : w.ValidOn G u v) (hmem : e ∈ w.edge) :
    e ∈ G.E := by
  match w with
  | nil x => simp at hmem
  | cons x e' (nil y) =>
    obtain ⟨rfl, rfl, hx⟩ := h
    simp only [cons_edge, nil_edge, mem_cons, not_mem_nil, or_false] at hmem
    subst hmem
    exact hx.edge_mem
  | cons x e' (cons y f w) =>
    obtain ⟨rfl, hbtw, hvalid⟩ := h
    rw [cons_edge, List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · exact hbtw.edge_mem
    · exact hvalid.mem_of_mem_edge hmem


end Walk

/-- A path is a walk with no duplicate vertices -/
def Path (α β : Type*) [DecidableEq α] := {w : Walk α β // w.vx.Nodup}

namespace Path
variable [DecidableEq α] {p : Path α β}


/-- A path is valid on a graph if its underlying walk is valid -/
def ValidOn (p : Path α β) (G : Graph α β) (u v : α) : Prop := p.val.ValidOn G u v

/-- List of vertices in a path -/
def vx (p : Path α β) : List α := p.val.vx

/-- List of edges in a path -/
def edge (p : Path α β) : List β := p.val.edge

/-- Length of a path -/
def length (p : Path α β) : ℕ := p.val.length

/-- Create a nil path -/
def nil (x : α) : Path α β := ⟨Walk.nil x, by simp⟩

/-- Create a path from a single edge between two vertices -/
def IsBetween.path (hbtw : G.IsBetween e u v) (hne : u ≠ v) : Path α β := ⟨hbtw.Walk, by simp [hne]⟩

/-- Create the reverse of a path -/
def reverse (p : Path α β) : Path α β := ⟨p.val.reverse, by simp [p.prop]⟩

lemma ValidOn.le {u v : α} {p : Path α β} (h : p.ValidOn G u v) (hle : G ≤ H) : p.ValidOn H u v :=
  Walk.ValidOn.le h hle

-- /-- If the endpoints of a path are connected in G via a valid path, they are connected in G -/
-- lemma connected_of_validOn (h : p.ValidOn G u v) : G.Connected u v :=
--   Walk.connected_of_validOn h

section disjoint

variable {ι : Type*}

/-- A collection of paths is internally disjoint if no vertex appears in more than one path
  except for the special two vertices u and v. (i.e. the endpoints of the paths. But this is not
  enforced in the definition) -/
def InternallyDisjoint (u v : α) (Ps : List (Path α β)) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.vx → x ∈ pj.vx → pi ≠ pj → x = u ∨ x = v

/-- A collection of paths is disjoint if no vertex appears in more than one path -/
def Disjoint (u v : α) (Ps : List (Path α β)) : Prop :=
  ∀ x pi pj, pi ∈ Ps → pj ∈ Ps → x ∈ pi.vx → x ∈ pj.vx → pi ≠ pj → x = u ∨ x = v

theorem Menger (G : Graph α β) [G.Finite] (u v : α) (hu : u ∈ G.V) (hv : v ∈ G.V)
    (hne : u ≠ v) (huv : ¬ G.Adj u v) (k : ℕ)
    (h : ∀ S : Set α, S.Finite → G.IsVxSeparator u v S → k ≤ S.ncard) :
    ∃ Ps : List (Path α β), (Ps.length = k) ∧ (∀ p ∈ Ps, p.ValidOn G u v) ∧ InternallyDisjoint u v Ps := by
  classical
  by_cases hk : k = 0
  · use [], by simp [hk], by simp, by simp [InternallyDisjoint]

  by_cases hadj : ∃ x : α, G.Adj u x ∧ G.Adj x v
  · obtain ⟨x, hux, hxv⟩ := hadj
    let G' := G[G.V \ {x}]
    have hG'le : G' ≤ G := induce_le G (by simp)
    have hu' : u ∈ G'.V := by
      simp only [induce_V, mem_diff, hu, mem_singleton_iff, true_and, G']
      rintro rfl
      exact huv hxv
    have hv' : v ∈ G'.V := by
      simp only [induce_V, mem_diff, hv, mem_singleton_iff, true_and, G']
      rintro rfl
      exact huv hux
    have huv' : ¬ G'.Adj u v := by
      contrapose! huv
      exact huv.of_Adj_induce
    obtain ⟨eux, heux⟩ := hux
    obtain ⟨exv, hexv⟩ := hxv
    let p : Path α β := ⟨((Walk.nil v).cons x exv).cons u eux, by simp [hne]; sorry⟩
    have hp : p.ValidOn G u v := ⟨rfl, heux, rfl, rfl, hexv⟩
    have hpvx : p.vx = [u, x, v] := rfl
    have hG'Fin : G'.Finite := finite_of_le_finite hG'le
    have hG'term : (G.E ∩ {e | ∀ (x_1 : α), G.Inc x_1 e → x_1 ∈ G.V ∧ ¬x_1 = x}).ncard + (k - 1) < G.E.ncard + k := by
      sorry
    have := Menger G' u v hu' hv' hne huv' (k-1) ?_
    obtain ⟨Ps, hlen, hPVd, hPs⟩ := this
    use p :: Ps, ?_, ?_
    · rintro y pi pj hpi hpj hyi hyj hpij
      by_cases hnepi : pi ≠ p ∧ pj ≠ p
      · have hpiPs : pi ∈ Ps := by simpa [hnepi.1] using hpi
        have hpjPs : pj ∈ Ps := by simpa [hnepi.2] using hpj
        exact hPs y pi pj hpiPs hpjPs hyi hyj hpij
      · wlog heqp : pi = p
        · apply this G u v hu hv hne huv k h hk x hG'le hu' hv' huv' eux heux exv hexv hp hpvx
            hG'Fin hG'term Ps hlen hPVd hPs y pj pi hpj hpi hyj hyi hpij.symm
            (by rw [and_comm] at hnepi; exact hnepi)
          push_neg at hnepi
          exact hnepi heqp
        subst pi
        simp only [hpvx, mem_cons, not_mem_nil, or_false] at hyi
        obtain rfl | rfl | rfl := hyi
        · left; rfl
        · rw [and_comm] at hnepi
          simp only [mem_cons, hpij.symm, false_or] at hpj
          specialize hPVd pj hpj
          have : y ∈ G'.V := hPVd.mem_of_mem_vx hyj
          simp [G'] at this
        · right; rfl
    · simp only [length_cons, hlen, G']
      omega
    · rintro p' hp'
      rw [List.mem_cons] at hp'
      obtain (rfl | hvalid) := hp'
      · exact hp
      · exact (hPVd p' hvalid).le hG'le
    · rintro s hsFin hSsepG'
      by_cases hxs : x ∈ s
      · refine (by omega : k - 1 ≤ k).trans (h s hsFin ?_)
        refine ⟨hSsepG'.not_mem_left, hSsepG'.not_mem_right, ?_⟩
        have := hSsepG'.not_connected
        simp only [induce_V, induce_induce_eq_induce_restrict, mem_diff, mem_singleton_iff,
          G'] at this
        convert this using 2
        rw [diff_diff, singleton_union, insert_eq_self.mpr hxs, eq_comm]
        apply subgraph_eq_induce
        simp +contextual only [mem_diff, setOf_subset_setOf, true_and, G']
        rintro e' h' x' hinc' rfl
        exact (h' x' hinc').2 hxs
      · specialize h (s ∪ {x}) (hsFin.union (by simp)) ?_
        · constructor
          · simp only [union_singleton, Set.mem_insert_iff, hSsepG'.not_mem_left, or_false, G']
            rintro rfl
            exact huv ⟨_, hexv⟩
          · simp only [union_singleton, Set.mem_insert_iff, hSsepG'.not_mem_right, or_false, G']
            rintro rfl
            exact huv ⟨_, heux⟩
          · convert hSsepG'.not_connected using 2
            simp only [union_singleton, induce_V, induce_induce_eq_induce_restrict, mem_diff,
              mem_singleton_iff, G']
            rw [diff_diff, singleton_union, eq_comm]
            apply subgraph_eq_induce
            simp +contextual only [mem_diff, Set.mem_insert_iff, not_or, setOf_subset_setOf,
              not_false_eq_true, and_self, implies_true, G']
        · rwa [ncard_union_eq (by simp [hxs]) hsFin, ncard_singleton, Nat.le_add_toss] at h
  · have : G.E.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro hE
      have := h ∅ (by simp) (by constructor <;> simp [hE, hne])
      simp only [ncard_empty, nonpos_iff_eq_zero] at this
      omega
    obtain ⟨e, he⟩ := this
    let G' := G{G.E \ {e}}
    have hG'le : G{G.E \ {e}} ≤ G := restrict_le G _
    by_cases h : ∀ (S : Set α), S.Finite → G{G.E \ {e}}.IsVxSeparator u v S → k ≤ S.ncard
    · -- Deleting the edge did not decrease k, so get the paths from the smaller graph
      have hG'term : (G.E ∩ (G.E \ {e})).ncard + k < G.E.ncard + k := by
        simp only [restrict_E, add_lt_add_iff_right]
        apply Set.ncard_lt_ncard ?_ Finite.edge_fin
        refine inter_ssubset_left_iff.mpr ?_
        rintro hsu
        have := hsu he
        simp at this
      have := Menger (G{G.E \ {e}}) u v hu hv hne (by contrapose! huv; exact huv.of_Adj_restrict) k h
      obtain ⟨Ps, hlen, hPVd, hPs⟩ := this
      use Ps, hlen
      constructor
      · rintro p hp
        exact (hPVd p hp).le hG'le
      · rintro pj hpj pi hpi x hx hx' hne
        refine hPs pj hpj pi hpi x ?_ ?_ hne
        · simpa using hx
        · simpa using hx'
    · -- Deleting the edge did decrease k, so contract instead
      simp only [not_forall, Classical.not_imp, not_le] at h
      obtain ⟨S, hSFin, hSsep, hcard⟩ := h
      obtain ⟨x, y, hxy⟩ := G.exist_IsBetween_of_mem he
      let G'' := G /[hxy.contractFun] {e}
      have hG''term : (G.E \ {e}).ncard < G.E.ncard :=
        Set.ncard_diff_singleton_lt_of_mem he Finite.edge_fin
      have hu'' : u ∈ G''.V := by
        use u, hu, IsBetween.contractFun_eq_self_of_not_inc hxy hnuinc
      have hv'' : v ∈ G''.V := by
        use v, hv, IsBetween.contractFun_eq_self_of_not_inc hxy hnvinc
      have := Menger G'' u v hu'' hv'' hne (by sorry) k ?_
      obtain ⟨Ps, hPVd, hPs⟩ := this
      obtain ⟨i, hi, hieq⟩ : ∃! p ∈ Ps, x ∈ p.vx := by
        sorry
      sorry
      sorry

termination_by G.E.ncard + k


-- theorem Menger_zero {k : ℕ} {G : Graph α β} [G.Finite] (u v : α) (hk0 : k = 0) :
--     ∃ Ps : List (Path α β), (∀ p ∈ Ps, p.ValidOn G u v) ∧ InternallyDisjoint u v Ps := by
--   use []
--   simp [InternallyDisjoint]

-- theorem Menger_succ {k : ℕ} (G : Graph α β) [G.Finite] (u v : α) (hu : u ∈ G.V) (hv : v ∈ G.V)
--     (hne : u ≠ v) (huv : ¬ G.Adj u v) (hkpos : 0 < k)
--     (h : ∀ S : Set α, S.Finite → G.IsVxSeparator u v S → k ≤ S.ncard) :
--     ∃ Ps : List (Path α β), (∀ p ∈ Ps, p.ValidOn G u v) ∧ InternallyDisjoint u v Ps := by
--   classical
--   by_cases heuv : ∃ e : β, e ∈ G.E ∧ ¬ G.Inc u e ∧ ¬ G.Inc v e
--   · -- There exists an edge that is not incident to u or v
--     -- Therefore, we can use del/contract to reduce the problem to a smaller graph
--     obtain ⟨e, he, hnuinc, hnvinc⟩ := heuv
--     have hG'le : G{G.E \ {e}} ≤ G := restrict_le G _
--     by_cases h : ∀ (S : Set α), S.Finite → G{G.E \ {e}}.IsVxSeparator u v S → k ≤ S.ncard
--     · -- Deleting the edge did not decrease k, so get the paths from the smaller graph
--       have hG'term : (G.E ∩ (G.E \ {e})).ncard + k < G.E.ncard + k := by
--         simp only [restrict_E, add_lt_add_iff_right]
--         apply Set.ncard_lt_ncard ?_ Finite.edge_fin
--         refine inter_ssubset_left_iff.mpr ?_
--         rintro hsu
--         have := hsu he
--         simp at this
--       have := Menger_succ (G{G.E \ {e}}) u v hu hv hne (by contrapose! huv; exact huv.of_Adj_restrict) hkpos h
--       obtain ⟨Ps, hPVd, hPs⟩ := this
--       use Ps
--       constructor
--       · rintro p hp
--         exact (hPVd p hp).le hG'le
--       · intro pj hpj pi hpi x hx hx' hne
--         refine hPs pj hpj pi hpi x ?_ ?_ hne
--         · simpa using hx
--         · simpa using hx'
--     · -- Deleting the edge did decrease k, so contract instead
--       simp only [not_forall, Classical.not_imp, not_le] at h
--       obtain ⟨S, hSFin, hSsep, hcard⟩ := h
--       obtain ⟨x, y, hxy⟩ := G.exist_IsBetween_of_mem he
--       let G'' := G /[hxy.contractFun] {e}
--       have hG''term : (G.E \ {e}).ncard < G.E.ncard :=
--         Set.ncard_diff_singleton_lt_of_mem he Finite.edge_fin
--       have hu'' : u ∈ G''.V := by
--         use u, hu, IsBetween.contractFun_eq_self_of_not_inc hxy hnuinc
--       have hv'' : v ∈ G''.V := by
--         use v, hv, IsBetween.contractFun_eq_self_of_not_inc hxy hnvinc
--       have := Menger_succ G'' u v hu'' hv'' hne (by sorry) hkpos ?_
--       obtain ⟨Ps, hPVd, hPs⟩ := this
--       obtain ⟨i, hi, hieq⟩ : ∃! p ∈ Ps, x ∈ p.vx := by
--         sorry
--       sorry
--       sorry
--   · -- No edge is not incident to u or v
--     -- So if there is no vertex adjacent to both u and v, then u and v are not connected
--     push_neg at heuv
--     by_cases hadj : ∃ x : α, G.Adj u x ∧ G.Adj x v
--     · -- There exists a vertex adjacent to both u and v
--       -- so get a path through that vertex
--       obtain ⟨x, hux, hxv⟩ := hadj
--       let G' := G[G.V \ {x}]
--       have hG'le : G' ≤ G := induce_le G Set.diff_subset
--       have hu' : u ∈ G'.V := by
--         simp only [induce_V, mem_diff, hu, mem_singleton_iff, true_and, G']
--         rintro rfl
--         exact huv hxv
--       have hv' : v ∈ G'.V := by
--         simp only [induce_V, mem_diff, hv, mem_singleton_iff, true_and, G']
--         rintro rfl
--         exact huv hux
--       have huv' : ¬ G'.Adj u v := by
--         contrapose! huv
--         exact huv.of_Adj_induce
--       have hG'Fin : G'.Finite := finite_of_le_finite hG'le
--       obtain ⟨eux, heux⟩ := hux
--       obtain ⟨exv, hexv⟩ := hxv
--       let p : Path α β := ⟨((Walk.nil v).cons x exv).cons u eux, by simp [hne]; sorry⟩
--       have hp : p.ValidOn G u v := ⟨rfl, heux, rfl, rfl, hexv⟩
--       have hpvx : p.vx = [u, x, v] := rfl
--       have hG'term : (G.E ∩ {e | ∀ (x_1 : α), G.Inc x_1 e → x_1 ∈ G.V ∧ ¬x_1 = x}).ncard + (k - 1) < G.E.ncard + k := by
--         suffices (G.E ∩ {e | ∀ (x_1 : α), G.Inc x_1 e → x_1 ∈ G.V ∧ ¬x_1 = x}).ncard ≤ G.E.ncard by omega
--         exact Set.ncard_le_ncard (fun e => by simp +contextual) Finite.edge_fin
--       have := Menger_succ G' (k := k-1) u v hu' hv' hne huv' sorry ?_
--       obtain ⟨Ps, hPVd, hPs⟩ := this
--       use p :: Ps, ?_
--       · rintro y pi pj hpi hpj hyi hyj hpij
--         by_cases h : pi ≠ p ∧ pj ≠ p
--         · sorry
--         · wlog h : pi = p
--           · sorry
--           subst pi
--           simp only [hpvx, mem_cons, not_mem_nil, or_false] at hyi
--           obtain rfl | rfl | rfl := hyi
--           · left; rfl
--           · sorry
--           · right; rfl
--       sorry
--       -- let Ps' : Fin k → G.Path u v := fun i ↦ Fin.cons sorry (fun i ↦ (Ps i).le hG'le) (i.cast (by sorry))
--       -- use Fin.cons sorry (fun i ↦ (Ps i).le hG'le)
--       sorry
--     · sorry
-- termination_by G.E.ncard + k


end disjoint

end Path

-- /-- Convert a walk to a path by deduplicating vertices -/
-- def Walk.toPath [DecidableEq α] (w : Walk α β) : Path α β :=
--   ⟨w.dedup, dedup_vx_nodup w⟩
