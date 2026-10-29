module

public import Theorem12Proof.GaussianComparisonKernel
import Mathlib.Tactic

/-!
# A small analytic perturbation of the upper half-plane

We choose the scale from the proved Gaussian first-moment bound, so no
numerical evaluation of that moment is needed. The perturbation is uniformly
close to the identity and bi-Lipschitz on the closed upper half-plane.
-/

@[expose] public section

open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal MeasureTheory ProbabilityTheory Topology

namespace ThreeOmittedValues

noncomputable def gaussianScale : ℝ := 1 / (4 * (1 + gaussianMoment))

theorem gaussianScale_pos : 0 < gaussianScale := by
  unfold gaussianScale
  have h := gaussianMoment_nonneg
  positivity

theorem gaussianScale_le_quarter : gaussianScale ≤ 1 / 4 := by
  unfold gaussianScale
  have h := gaussianMoment_nonneg
  apply (div_le_iff₀ (by positivity : 0 < 4 * (1 + gaussianMoment))).2
  nlinarith

theorem gaussianScale_mul_moment_le_quarter : gaussianScale * gaussianMoment ≤ 1 / 4 := by
  unfold gaussianScale
  have h := gaussianMoment_nonneg
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (1 + gaussianMoment))).2
  nlinarith

noncomputable def gaussianPerturbation (z : ℂ) : ℂ :=
  z + (gaussianScale : ℂ) * gaussianKernel z

theorem gaussianPerturbation_differentiable : Differentiable ℂ gaussianPerturbation := by
  unfold gaussianPerturbation
  exact differentiable_id.add (gaussianKernel_differentiable.const_mul _)

theorem gaussianPerturbation_displacement {z : ℂ} (hz : 0 ≤ z.im) :
    ‖gaussianPerturbation z - z‖ ≤ gaussianScale := by
  simp only [gaussianPerturbation, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos gaussianScale_pos]
  have h := gaussianKernel_norm_le_one hz
  nlinarith [gaussianScale_pos]

theorem gaussianPerturbation_bilipschitz {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    (1 / 2 : ℝ) * ‖z - w‖ ≤ ‖gaussianPerturbation z - gaussianPerturbation w‖ ∧
      ‖gaussianPerturbation z - gaussianPerturbation w‖ ≤ (3 / 2 : ℝ) * ‖z - w‖ := by
  have hkernel := gaussianKernel_lipschitz_upper hz hw
  have hscaled : ‖(gaussianScale : ℂ) * (gaussianKernel z - gaussianKernel w)‖ ≤
      (1 / 4 : ℝ) * ‖z - w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos gaussianScale_pos]
    calc
      gaussianScale * ‖gaussianKernel z - gaussianKernel w‖ ≤
          gaussianScale * (gaussianMoment * ‖z - w‖) :=
        mul_le_mul_of_nonneg_left hkernel gaussianScale_pos.le
      _ = (gaussianScale * gaussianMoment) * ‖z - w‖ := by ring
      _ ≤ (1 / 4 : ℝ) * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right gaussianScale_mul_moment_le_quarter (norm_nonneg _)
  have hid : gaussianPerturbation z - gaussianPerturbation w =
      (z - w) + (gaussianScale : ℂ) * (gaussianKernel z - gaussianKernel w) := by
    simp only [gaussianPerturbation]
    ring
  have hupper := norm_add_le (z - w) ((gaussianScale : ℂ) *
    (gaussianKernel z - gaussianKernel w))
  have hlower := norm_sub_le (gaussianPerturbation z - gaussianPerturbation w)
    ((gaussianScale : ℂ) * (gaussianKernel z - gaussianKernel w))
  rw [← hid] at hupper
  have heq : gaussianPerturbation z - gaussianPerturbation w -
      (gaussianScale : ℂ) * (gaussianKernel z - gaussianKernel w) = z - w := by
    rw [hid]
    ring
  rw [heq] at hlower
  constructor <;> nlinarith [norm_nonneg (z - w)]

theorem gaussianPerturbation_injOn :
    InjOn gaussianPerturbation {z : ℂ | 0 ≤ z.im} := by
  intro z hz w hw heq
  have h := (gaussianPerturbation_bilipschitz hz hw).1
  rw [heq, sub_self, norm_zero] at h
  have : ‖z - w‖ = 0 := by nlinarith [norm_nonneg (z - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end ThreeOmittedValues
