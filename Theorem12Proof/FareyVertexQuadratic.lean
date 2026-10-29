module

public import Theorem12Proof.FareyVertexEdges
import Mathlib.Tactic

/-!
# Quadratic approach to a Farey vertex

Near a vertex the graph follows an incident semicircle whose other endpoint
is a definite distance away. Consequently horizontal displacement from the
vertex is bounded by a constant times the squared height of the graph.
-/

@[expose] public section

open Metric Set

namespace ThreeOmittedValues

theorem pastedFarey_vertex_quadratic (levels : ℤ → ℕ) (r : ℝ)
    (hr0 : pastedFareyHeight levels r = 0) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ x : ℝ, |x - r| < ε →
      |x - r| ≤ C * (pastedFareyHeight levels x) ^ 2 := by
  obtain ⟨δ, hδ, hisol⟩ := pastedFarey_vertex_isolated levels r
  refine ⟨δ / 2, 2 / δ, half_pos hδ, div_pos (by norm_num) hδ, ?_⟩
  intro x hx
  have hxδ : |x - r| < δ := by linarith
  obtain ⟨n, e, he, hl, hr, hincident, hsquare⟩ :=
    pastedFarey_edge_near_vertex levels hr0 hδ hisol hxδ
  let L : ℝ := (n : ℝ) + endpointCoordinate e.left
  let R : ℝ := (n : ℝ) + endpointCoordinate e.right
  have hLR : L < R := by
    have h := sternBrocotEdges_strict (levels n) he
    dsimp [L, R]
    linarith
  have hends := pastedFarey_edge_endpoints_zero levels n he
  have hxclose := abs_lt.mp hx
  have hmul : δ * |x - r| ≤ 2 * (pastedFareyHeight levels x) ^ 2 := by
    rcases hincident with hleft | hright
    · have hrL : r = L := hleft
      have hfar : δ ≤ R - r := by
        by_contra hnot
        have hRball : R ∈ ball r δ := by
          rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < R - r)]
          linarith
        have heq := hisol R hRball hends.2
        linarith
      have hremain : δ / 2 ≤ R - x := by linarith [hxclose.2]
      have hxnonneg : 0 ≤ x - r := by linarith
      have hprod := mul_le_mul_of_nonneg_left hremain hxnonneg
      have habs : |x - r| = x - r := abs_of_nonneg hxnonneg
      rw [habs]
      dsimp [L, R] at *
      nlinarith [hprod]
    · have hrR : r = R := hright
      have hfar : δ ≤ r - L := by
        by_contra hnot
        have hLball : L ∈ ball r δ := by
          rw [mem_ball, Real.dist_eq, abs_of_neg (by linarith : L - r < 0)]
          linarith
        have heq := hisol L hLball hends.1
        linarith
      have hremain : δ / 2 ≤ x - L := by linarith [hxclose.1]
      have hxnonneg : 0 ≤ r - x := by linarith
      have hprod := mul_le_mul_of_nonneg_right hremain hxnonneg
      have habs : |x - r| = r - x := by rw [abs_of_nonpos (by linarith : x - r ≤ 0)]; ring
      rw [habs]
      dsimp [L, R] at *
      nlinarith [hprod]
  have hdiv : |x - r| ≤ (2 * (pastedFareyHeight levels x) ^ 2) / δ :=
    (le_div_iff₀ hδ).2 (by simpa only [mul_comm] using hmul)
  calc
    _ ≤ (2 * (pastedFareyHeight levels x) ^ 2) / δ := hdiv
    _ = (2 / δ) * (pastedFareyHeight levels x) ^ 2 := by ring

end ThreeOmittedValues
