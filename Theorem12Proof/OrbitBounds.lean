module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Height bounds for the selected orbit points

The elementary estimates here are the real-variable part of equation (12)
in section 5 of arXiv:2608.26062v2.
-/

@[expose] public section

namespace ThreeOmittedValues

/-- Uniform upper and lower bounds for the height of a selected orbit point. -/
theorem selected_height_bounds {m d ξ ν : ℝ}
    (hm : 0 < m) (hd0 : 0 ≤ d) (hd : d ≤ 2 * m) (hν : 0 < ν) :
    ν / (4 * ((|ξ| + 1) ^ 2 + ν ^ 2) * m ^ 2) ≤
        ν / ((2 * m * ξ + d) ^ 2 + (2 * m * ν) ^ 2) ∧
      ν / ((2 * m * ξ + d) ^ 2 + (2 * m * ν) ^ 2) ≤
        1 / (4 * ν * m ^ 2) := by
  have htwo : 0 ≤ 2 * m := by positivity
  have habs : |2 * m * ξ + d| ≤ 2 * m * (|ξ| + 1) := by
    calc
      |2 * m * ξ + d| ≤ |2 * m * ξ| + |d| := abs_add_le _ _
      _ = 2 * m * |ξ| + d := by rw [abs_mul, abs_of_nonneg htwo, abs_of_nonneg hd0]
      _ ≤ 2 * m * (|ξ| + 1) := by nlinarith
  have hsquare : (2 * m * ξ + d) ^ 2 ≤ (2 * m * (|ξ| + 1)) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (2 * m * ξ + d)) habs 2
    simpa only [sq_abs] using h
  have hdenpos : 0 < (2 * m * ξ + d) ^ 2 + (2 * m * ν) ^ 2 := by positivity
  have hdenupper : (2 * m * ξ + d) ^ 2 + (2 * m * ν) ^ 2 ≤
      4 * ((|ξ| + 1) ^ 2 + ν ^ 2) * m ^ 2 := by
    nlinarith [hsquare]
  have hdenlower : 4 * m ^ 2 * ν ^ 2 ≤
      (2 * m * ξ + d) ^ 2 + (2 * m * ν) ^ 2 := by
    nlinarith [sq_nonneg (2 * m * ξ + d)]
  constructor
  · apply (div_le_div_iff₀ (by positivity) hdenpos).2
    exact mul_le_mul_of_nonneg_left hdenupper hν.le
  · apply (div_le_div_iff₀ hdenpos (by positivity)).2
    have hmul : ν * (4 * ν * m ^ 2) = 4 * m ^ 2 * ν ^ 2 := by ring
    simpa only [hmul, one_mul] using hdenlower

end ThreeOmittedValues
