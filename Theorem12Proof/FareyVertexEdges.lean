module

public import Theorem12Proof.FareyVertexLocalFinite
import Mathlib.Tactic

/-!
# Edges adjacent to a Farey vertex

Near any vertex, every semicircle that contributes to the pasted graph is
incident to that vertex. Its other endpoint stays a definite distance away.
-/

@[expose] public section

open Metric Set

namespace ThreeOmittedValues

theorem pastedFarey_vertex_isolated (levels : ℤ → ℕ) (r : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ ball r δ, pastedFareyHeight levels x = 0 → x = r := by
  let V : Set ℝ := ball r 1 ∩ {x : ℝ | pastedFareyHeight levels x = 0}
  have hfin : V.Finite := pastedFarey_zeros_locally_finite levels r
  have hclosed : IsClosed (V \ {r}) := (hfin.subset sdiff_subset).isClosed
  have hr : r ∈ (V \ {r})ᶜ := by simp
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl r hr
  refine ⟨min 1 δ, lt_min (by norm_num) hδ, ?_⟩
  intro x hx hx0
  have hx1 : x ∈ ball r 1 := (ball_subset_ball (min_le_left _ _)) hx
  have hxδ : x ∈ ball r δ := (ball_subset_ball (min_le_right _ _)) hx
  have hnot := hδsub hxδ
  by_contra hne
  exact hnot ⟨⟨hx1, hx0⟩, by simpa using hne⟩

theorem pastedFarey_edge_endpoints_zero (levels : ℤ → ℕ) (n : ℤ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges (levels n)) :
    pastedFareyHeight levels ((n : ℝ) + endpointCoordinate e.left) = 0 ∧
      pastedFareyHeight levels ((n : ℝ) + endpointCoordinate e.right) = 0 := by
  have hc := sternBrocotEdges_coordinates_in_unit (levels n) he
  constructor
  · have hx : (n : ℝ) + endpointCoordinate e.left ∈ Icc (n : ℝ) ((n : ℝ) + 1) := by
      constructor <;> linarith [hc.1.1, hc.1.2]
    rw [pastedFareyHeight_eq_on_unit levels n hx]
    have heq : (n : ℝ) + endpointCoordinate e.left - n = endpointCoordinate e.left := by ring
    rw [heq]
    exact sternBrocot_chainHeight_eq_zero_at_endpoint (levels n) ⟨e, he, Or.inl rfl⟩
  · have hx : (n : ℝ) + endpointCoordinate e.right ∈ Icc (n : ℝ) ((n : ℝ) + 1) := by
      constructor <;> linarith [hc.2.1, hc.2.2]
    rw [pastedFareyHeight_eq_on_unit levels n hx]
    have heq : (n : ℝ) + endpointCoordinate e.right - n = endpointCoordinate e.right := by ring
    rw [heq]
    exact sternBrocot_chainHeight_eq_zero_at_endpoint (levels n) ⟨e, he, Or.inr rfl⟩

/-- A zero lying on an edge is one of its endpoints. -/
theorem pastedFarey_zero_on_edge (levels : ℤ → ℕ) (n : ℤ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges (levels n)) {r : ℝ}
    (hrleft : (n : ℝ) + endpointCoordinate e.left ≤ r)
    (hrright : r ≤ (n : ℝ) + endpointCoordinate e.right)
    (hr0 : pastedFareyHeight levels r = 0) :
    r = (n : ℝ) + endpointCoordinate e.left ∨
      r = (n : ℝ) + endpointCoordinate e.right := by
  have hc := sternBrocotEdges_coordinates_in_unit (levels n) he
  have hrunit : r ∈ Icc (n : ℝ) ((n : ℝ) + 1) := by
    constructor <;> linarith [hc.1.1, hc.2.2]
  have hl : endpointCoordinate e.left ≤ r - n := by linarith
  have hr : r - n ≤ endpointCoordinate e.right := by linarith
  have heq := sternBrocot_chainHeight_eq_edge (levels n) he hl hr
  have hzero : edgeHeight e (r - n) = 0 := by
    rw [← heq, ← pastedFareyHeight_eq_on_unit levels n hrunit]
    exact hr0
  have hsquare := edgeHeight_sq_of_inside e hl hr
  rw [hzero, zero_pow (by norm_num)] at hsquare
  rcases mul_eq_zero.mp hsquare.symm with hleft | hright
  · left
    linarith
  · right
    linarith

theorem pastedFarey_edge_near_vertex (levels : ℤ → ℕ) {r δ x : ℝ}
    (hr0 : pastedFareyHeight levels r = 0) (hδ : 0 < δ)
    (hisol : ∀ y ∈ ball r δ, pastedFareyHeight levels y = 0 → y = r)
    (hx : |x - r| < δ) :
    ∃ (n : ℤ) (e : RationalEdge), e ∈ sternBrocotEdges (levels n) ∧
      (n : ℝ) + endpointCoordinate e.left ≤ x ∧
      x ≤ (n : ℝ) + endpointCoordinate e.right ∧
      (r = (n : ℝ) + endpointCoordinate e.left ∨
        r = (n : ℝ) + endpointCoordinate e.right) ∧
      pastedFareyHeight levels x ^ 2 =
        (x - ((n : ℝ) + endpointCoordinate e.left)) *
          (((n : ℝ) + endpointCoordinate e.right) - x) := by
  let n : ℤ := ⌊x⌋
  have hx0 : (0 : ℝ) ≤ x - n := sub_nonneg.mpr (Int.floor_le x)
  have hx1 : x - (n : ℝ) ≤ 1 := by
    have hfloor : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
    linarith
  obtain ⟨e, he, hl, hr⟩ := sternBrocotEdges_cover (levels n) hx0 hx1
  let L : ℝ := (n : ℝ) + endpointCoordinate e.left
  let R : ℝ := (n : ℝ) + endpointCoordinate e.right
  have hLx : L ≤ x := by dsimp [L]; linarith
  have hxR : x ≤ R := by dsimp [R]; linarith
  have hLR : L < R := by
    have := sternBrocotEdges_strict (levels n) he
    dsimp [L, R]
    linarith
  have hends := pastedFarey_edge_endpoints_zero levels n he
  have hclose : -δ < x - r ∧ x - r < δ := abs_lt.mp hx
  have hincident : r = L ∨ r = R := by
    by_cases hrl : r < L
    · have hLball : L ∈ ball r δ := by
        rw [mem_ball, Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ L - r)]
        linarith
      exact Or.inl (hisol L hLball hends.1).symm
    · by_cases hrr : R < r
      · have hRball : R ∈ ball r δ := by
          rw [mem_ball, Real.dist_eq, abs_of_nonpos (by linarith : R - r ≤ 0)]
          linarith
        exact Or.inr (hisol R hRball hends.2).symm
      · exact pastedFarey_zero_on_edge levels n he (by dsimp [L] at *; linarith)
          (by dsimp [R] at *; linarith) hr0
  have hxunit : x ∈ Icc (n : ℝ) ((n : ℝ) + 1) := by
    constructor
    · exact Int.floor_le x
    · exact (Int.lt_floor_add_one x).le
  have hxeq := sternBrocot_chainHeight_eq_edge (levels n) he hl hr
  have hsquare := edgeHeight_sq_of_inside e hl hr
  rw [pastedFareyHeight_eq_on_unit levels n hxunit, hxeq, hsquare]
  refine ⟨n, e, he, hLx, hxR, hincident, ?_⟩
  ring

end ThreeOmittedValues
