module

public import Theorem12Proof.FareyCompactLocal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-!
# The two ends of a compactified graph agree

After the Cayley transform, both ends of a nonnegative graph converge to
the same boundary point `1`. This is independent of the graph's height.
-/

@[expose] public section

open Complex Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem compactGraph_norm_sub_one {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x) (x : ℝ) :
    ‖halfPlaneToCayley (graphMap h x) - 1‖ =
      2 * ‖graphMap h x + Complex.I‖⁻¹ := by
  have hne := graph_denominator_ne hh x
  have heq : halfPlaneToCayley (graphMap h x) - 1 =
      (-2 * Complex.I) / (graphMap h x + Complex.I) := by
    unfold halfPlaneToCayley
    field_simp
    ring
  rw [heq]
  simp [norm_div, norm_mul, div_eq_mul_inv]

theorem compactGraph_tendsto_one {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x)
    {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => |x|) l atTop) :
    Tendsto (halfPlaneToCayley ∘ graphMap h) l (𝓝 1) := by
  have hbound (x : ℝ) : |x| ≤ ‖graphMap h x + Complex.I‖ := by
    have h := Complex.abs_re_le_norm (graphMap h x + Complex.I)
    simpa only [Complex.add_re, graphMap_re, Complex.I_re, add_zero] using h
  have hnorm : Tendsto (fun x : ℝ => ‖graphMap h x + Complex.I‖) l atTop :=
    tendsto_atTop_mono hbound hl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hinv := hnorm.inv_tendsto_atTop
  have hscaled : Tendsto (fun x : ℝ => (2 : ℝ) * ‖graphMap h x + Complex.I‖⁻¹) l (𝓝 0) := by
    simpa only [mul_zero] using! hinv.const_mul (2 : ℝ)
  simpa only [Function.comp_apply, compactGraph_norm_sub_one hh, mul_zero] using hscaled

theorem compactFareyGraph_tendsto_one_atTop (levels : ℤ → ℕ) :
    Tendsto (halfPlaneToCayley ∘ graphMap (pastedFareyHeight levels)) atTop (𝓝 1) :=
  compactGraph_tendsto_one (pastedFareyHeight_nonneg levels) tendsto_abs_atTop_atTop

theorem compactFareyGraph_tendsto_one_atBot (levels : ℤ → ℕ) :
    Tendsto (halfPlaneToCayley ∘ graphMap (pastedFareyHeight levels)) atBot (𝓝 1) :=
  compactGraph_tendsto_one (pastedFareyHeight_nonneg levels) tendsto_abs_atBot_atTop

end ThreeOmittedValues
