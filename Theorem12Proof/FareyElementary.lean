module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Elementary geometry of adjacent Farey fractions

These lemmas isolate the denominator and semicircle-height estimates used to
place the Farey boundary below the comparison graph. They do not construct
the Farey sequence or its infinite boundary path.
-/

@[expose] public section

namespace ThreeOmittedValues

/-- If positive denominators satisfy `b + d > L`, then their product is at
least `L`. -/
theorem farey_denominator_product_bound {b d L : ℕ}
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hbd : L < b + d) : L ≤ b * d := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsum : L + 1 ≤ b + d := by omega
  have hsum' : (L : ℝ) + 1 ≤ (b : ℝ) + d := by exact_mod_cast hsum
  have hp : 0 ≤ ((b : ℝ) - 1) * ((d : ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hreal : (L : ℝ) ≤ (b : ℝ) * d := by nlinarith [hp]
  exact_mod_cast hreal

/-- The distance between two Farey-neighbor fractions is `1/(b*d)`. -/
theorem farey_neighbor_gap {a b c d : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hdet : b * c - a * d = 1) :
    c / d - a / b = 1 / (b * d) := by
  field_simp [ne_of_gt hb, ne_of_gt hd]
  linear_combination hdet

/-- A Farey semicircle whose denominator product is at least `L` has
height at most `1/(2L)`. -/
theorem farey_semicircle_height_le {b d L : ℝ}
    (hL : 0 < L) (_hb : 0 < b) (_hd : 0 < d) (hprod : L ≤ b * d) :
    1 / (2 * b * d) ≤ 1 / (2 * L) := by
  have hden : 2 * L ≤ 2 * b * d := by nlinarith [hprod]
  exact one_div_le_one_div_of_le (by positivity) hden

end ThreeOmittedValues
