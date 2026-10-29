module

public import Theorem12Proof.HalfPlaneWeight
public import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic

/-!
# Schwarz comparison of half-plane Blaschke weights

For a holomorphic self-map of the upper half-plane fixing `i`, its output
Blaschke weight dominates one quarter of its input weight. This elementary
comparison can replace a separate Green-function monotonicity theorem in the
normalized comparison-domain argument.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem cayley_disk_weight_le_four_halfPlane {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) :
    1 - ‖w‖ ≤ 4 * blaschkeWeight (cayleyToHalfPlane w) := by
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
  rw [hweight, ← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < 2 * (1 + ‖w‖ ^ 2))).2
  have hfac : 0 ≤ 1 - ‖w‖ := by linarith
  have hfac₂ : 0 ≤ 1 + 2 * ‖w‖ - ‖w‖ ^ 2 := by
    have hn := norm_nonneg w
    nlinarith
  have hprod := mul_nonneg hfac hfac₂
  nlinarith

theorem halfPlane_disk_weight_le_four {z : ℂ} (hz : 0 < z.im) :
    1 - ‖halfPlaneToCayley z‖ ≤ 4 * blaschkeWeight z := by
  have h := cayley_disk_weight_le_four_halfPlane (halfPlaneToCayley_mem_ball hz)
  simpa only [cayleyToHalfPlane_halfPlaneToCayley hz] using h

/-- A normalized half-plane self-map loses at most a fixed factor in the
Blaschke weight. -/
theorem halfPlane_blaschkeWeight_schwarz {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.im})
    (hmaps : ∀ z : ℂ, 0 < z.im → 0 < (H z).im)
    (hfix : H Complex.I = Complex.I) {z : ℂ} (hz : 0 < z.im) :
    blaschkeWeight z ≤ 4 * blaschkeWeight (H z) := by
  let F : ℂ → ℂ := fun w => halfPlaneToCayley (H (cayleyToHalfPlane w))
  have hcay : DifferentiableOn ℂ cayleyToHalfPlane (ball (0 : ℂ) 1) := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    unfold cayleyToHalfPlane
    fun_prop (disch := exact one_sub_ne_zero_of_mem_ball hw)
  have hsrc : MapsTo cayleyToHalfPlane (ball (0 : ℂ) 1) {z : ℂ | 0 < z.im} := by
    intro w hw
    exact cayleyToHalfPlane_im_pos hw
  have hret : DifferentiableOn ℂ halfPlaneToCayley {z : ℂ | 0 < z.im} := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    unfold halfPlaneToCayley
    fun_prop (disch := exact add_I_ne_zero_of_im_pos hw)
  have hHmaps : MapsTo H {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} := by
    intro w hw
    exact hmaps w hw
  have hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1) :=
    hret.comp (hH.comp hcay hsrc) (hHmaps.comp hsrc)
  have hFmaps : MapsTo F (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    intro w hw
    apply ball_subset_closedBall
    exact halfPlaneToCayley_mem_ball (hmaps _ (cayleyToHalfPlane_im_pos hw))
  have hFzero : F 0 = 0 := by
    simp [F, cayleyToHalfPlane, hfix, halfPlaneToCayley]
  have hnorm := Complex.norm_le_norm_of_mapsTo_ball hF hFmaps hFzero
    ((mem_ball_zero_iff.mp (halfPlaneToCayley_mem_ball hz)))
  have hnorm' : ‖halfPlaneToCayley (H z)‖ ≤ ‖halfPlaneToCayley z‖ := by
    simpa only [F, cayleyToHalfPlane_halfPlaneToCayley hz] using hnorm
  have hleft := halfPlane_blaschkeWeight_le_cayley hz
  have hright := halfPlane_disk_weight_le_four (hmaps z hz)
  linarith

end ThreeOmittedValues
