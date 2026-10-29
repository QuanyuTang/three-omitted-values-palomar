module

public import Theorem12Proof.FareyCompactEnds
import Mathlib.Tactic

/-!
# The compactified graph is an embedded real line

The Cayley transform is injective wherever its denominator is nonzero,
and a real graph has injective real-coordinate projection.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem halfPlaneToCayley_injective_of_denominators {z w : ℂ}
    (hz : z + Complex.I ≠ 0) (hw : w + Complex.I ≠ 0)
    (hzw : halfPlaneToCayley z = halfPlaneToCayley w) : z = w := by
  have hdiff : halfPlaneToCayley z - halfPlaneToCayley w =
      2 * Complex.I * (z - w) / ((z + Complex.I) * (w + Complex.I)) := by
    unfold halfPlaneToCayley
    field_simp
    ring
  have hzero : 2 * Complex.I * (z - w) / ((z + Complex.I) * (w + Complex.I)) = 0 := by
    rw [← hdiff, hzw, sub_self]
  have hnum : 2 * Complex.I * (z - w) = 0 :=
    (div_eq_zero_iff.mp hzero).resolve_right (mul_ne_zero hz hw)
  have hfactor : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hnum).resolve_left hfactor)

theorem halfPlaneToCayley_ne_one_of_denominator {z : ℂ} (hz : z + Complex.I ≠ 0) :
    halfPlaneToCayley z ≠ 1 := by
  intro heq
  have heq' : z - Complex.I = 1 * (z + Complex.I) := (div_eq_iff hz).1 heq
  have him := congrArg Complex.im heq'
  simp only [Complex.sub_im, Complex.add_im, Complex.I_im, one_mul] at him
  linarith

theorem compactGraph_injective {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x) :
    Function.Injective (halfPlaneToCayley ∘ graphMap h) := by
  intro x y hxy
  have heq : graphMap h x = graphMap h y :=
    halfPlaneToCayley_injective_of_denominators (graph_denominator_ne hh x)
      (graph_denominator_ne hh y) hxy
  have hre := congrArg Complex.re heq
  simpa only [graphMap_re] using hre

theorem compactGraph_ne_one {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x) (x : ℝ) :
    (halfPlaneToCayley ∘ graphMap h) x ≠ 1 :=
  halfPlaneToCayley_ne_one_of_denominator (graph_denominator_ne hh x)

theorem compactGraph_continuous {h : ℝ → ℝ} (hh : Continuous h) (h0 : ∀ x, 0 ≤ h x) :
    Continuous (halfPlaneToCayley ∘ graphMap h) := by
  change Continuous (fun x : ℝ => (graphMap h x - Complex.I) / (graphMap h x + Complex.I))
  have hg := graphMap_continuous hh
  exact (hg.sub continuous_const).div (hg.add continuous_const) (graph_denominator_ne h0)

end ThreeOmittedValues
