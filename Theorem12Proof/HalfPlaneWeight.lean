module

public import Theorem12Proof.NoWanderingDomains.Hyperbolic.DiskModel.DiskMetric
public import Theorem12Proof.Reflection
import Mathlib.Tactic

/-!
# Comparison of the half-plane and disk Blaschke weights

The formulas for the Cayley transform come from the attributed
`NoWanderingDomains` development. The estimate below is elementary.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem cayley_halfPlane_blaschkeWeight_le {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    blaschkeWeight (cayleyToHalfPlane w) ≤ 1 - ‖w‖ := by
  have hw1 : ‖w‖ < 1 := by simpa only [mem_ball_zero_iff] using hw
  have hd : ‖(1 : ℂ) - w‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (one_sub_ne_zero_of_mem_ball hw)
  have hid : ‖(1 : ℂ) - w‖ ^ 2 + ‖(1 : ℂ) + w‖ ^ 2 =
      2 * (1 + ‖w‖ ^ 2) := by
    rw [← Complex.normSq_eq_norm_sq ((1 : ℂ) - w),
      ← Complex.normSq_eq_norm_sq ((1 : ℂ) + w), ← Complex.normSq_eq_norm_sq w]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hnorm : ‖cayleyToHalfPlane w‖ ^ 2 =
      ‖(1 : ℂ) + w‖ ^ 2 / ‖(1 : ℂ) - w‖ ^ 2 := by
    simp only [cayleyToHalfPlane, norm_div, norm_mul, Complex.norm_I, one_mul, div_pow]
  have hden : 1 + ‖cayleyToHalfPlane w‖ ^ 2 =
      2 * (1 + ‖w‖ ^ 2) / ‖(1 : ℂ) - w‖ ^ 2 := by
    rw [hnorm]
    field_simp
    linarith [hid]
  have hweight : blaschkeWeight (cayleyToHalfPlane w) =
      (1 - ‖w‖ ^ 2) / (2 * (1 + ‖w‖ ^ 2)) := by
    rw [blaschkeWeight, abs_of_pos (cayleyToHalfPlane_im_pos hw),
      cayleyToHalfPlane_im, hden]
    field_simp
  rw [hweight]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + ‖w‖ ^ 2))).2
  have hfac : 0 ≤ 1 - ‖w‖ := by linarith
  have hmul : 0 ≤ ‖w‖ ^ 2 * (1 - ‖w‖) := mul_nonneg (sq_nonneg _) hfac
  nlinarith [sq_nonneg (1 - ‖w‖)]

theorem halfPlane_blaschkeWeight_le_cayley {z : ℂ} (hz : 0 < z.im) :
    blaschkeWeight z ≤ 1 - ‖halfPlaneToCayley z‖ := by
  have h := cayley_halfPlane_blaschkeWeight_le (halfPlaneToCayley_mem_ball hz)
  simpa only [cayleyToHalfPlane_halfPlaneToCayley hz] using h

end ThreeOmittedValues
