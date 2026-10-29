module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic

/-!
# A Gaussian comparison kernel

We integrate over the positive half of a centered Gaussian of variance two.
Its complex moment-generating function gives an entire function; later
estimates will be restricted to the closed upper half-plane.
-/

@[expose] public section

open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal MeasureTheory ProbabilityTheory Topology

namespace ThreeOmittedValues

noncomputable def positiveGaussian : Measure ℝ :=
  (gaussianReal 0 (2 : ℝ≥0)).restrict (Ioi 0)

theorem positiveGaussian_expSet : integrableExpSet id positiveGaussian = univ := by
  ext t
  simp only [mem_univ, iff_true, integrableExpSet, mem_ofPred_eq, id_eq]
  exact (integrable_exp_mul_gaussianReal (μ := 0) (v := (2 : ℝ≥0)) t).mono_measure
    Measure.restrict_le_self

noncomputable def gaussianKernel (z : ℂ) : ℂ :=
  Complex.I * complexMGF id positiveGaussian (Complex.I * z)

theorem gaussianKernel_differentiable : Differentiable ℂ gaussianKernel := by
  have hmgf : Differentiable ℂ (complexMGF id positiveGaussian) := by
    have h := differentiableOn_complexMGF (X := id) (μ := positiveGaussian)
    simpa [positiveGaussian_expSet, differentiableOn_univ] using h
  unfold gaussianKernel
  fun_prop

noncomputable def gaussianMoment : ℝ := ∫ u : ℝ, |u| ∂positiveGaussian

theorem positiveGaussian_integrable_abs : Integrable (fun u : ℝ => |u|) positiveGaussian := by
  have hzero : (0 : ℝ) ∈ interior (integrableExpSet id positiveGaussian) := by
    simp [positiveGaussian_expSet]
  simpa using integrable_pow_abs_of_mem_interior_integrableExpSet hzero 1

theorem gaussianMoment_nonneg : 0 ≤ gaussianMoment :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem gaussianKernel_hasDerivAt (z : ℂ) :
    HasDerivAt gaussianKernel
      (-(∫ u : ℝ, (u : ℂ) * Complex.exp ((Complex.I * z) * u) ∂positiveGaussian)) z := by
  have hz : (Complex.I * z).re ∈ interior (integrableExpSet id positiveGaussian) := by
    simp [positiveGaussian_expSet]
  have h := (hasDerivAt_complexMGF (X := id) (μ := positiveGaussian) hz).comp z
    ((hasDerivAt_id z).const_mul Complex.I)
  have h' := h.const_mul Complex.I
  convert h' using 1
  · rfl
  · simp only [id_eq, mul_one]
    calc
      -(∫ u : ℝ, (u : ℂ) * Complex.exp ((Complex.I * z) * u) ∂positiveGaussian) =
          Complex.I ^ 2 * (∫ u : ℝ, (u : ℂ) * Complex.exp ((Complex.I * z) * u)
            ∂positiveGaussian) := by rw [Complex.I_sq]; ring
      _ = _ := by ring

theorem gaussianKernel_deriv_bound {z : ℂ} (hz : 0 ≤ z.im) :
    ‖deriv gaussianKernel z‖ ≤ gaussianMoment := by
  rw [(gaussianKernel_hasDerivAt z).deriv, norm_neg]
  unfold gaussianMoment
  apply norm_integral_le_of_norm_le positiveGaussian_integrable_abs
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have he : ‖Complex.exp ((Complex.I * z) * (u : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_sub]
    nlinarith
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg u) he

theorem gaussianKernel_lipschitz_upper {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    ‖gaussianKernel z - gaussianKernel w‖ ≤ gaussianMoment * ‖z - w‖ := by
  exact (convex_halfSpace_im_ge 0).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => gaussianKernel_differentiable.differentiableAt)
    (fun _ hx => gaussianKernel_deriv_bound hx) hw hz

theorem gaussianKernel_norm_le_one {z : ℂ} (hz : 0 ≤ z.im) :
    ‖gaussianKernel z‖ ≤ 1 := by
  letI : IsFiniteMeasure positiveGaussian := by
    unfold positiveGaussian
    infer_instance
  have hbound : ∀ᵐ (u : ℝ) ∂positiveGaussian,
      ‖Complex.exp ((Complex.I * z) * (u : ℂ))‖ ≤ 1 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Complex.norm_exp, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_sub]
    nlinarith [le_of_lt hu]
  have hint := norm_integral_le_of_norm_le (μ := positiveGaussian)
    (integrable_const (1 : ℝ)) hbound
  have hmass : (∫ _u : ℝ, (1 : ℝ) ∂positiveGaussian) ≤ 1 := by
    have hm := integral_mono_measure
      (show positiveGaussian ≤ gaussianReal 0 (2 : ℝ≥0) from Measure.restrict_le_self)
      (Filter.Eventually.of_forall (fun _ : ℝ => (show (0 : ℝ) ≤ 1 by norm_num)))
      (integrable_const (1 : ℝ))
    simpa using hm
  simpa [gaussianKernel, complexMGF, norm_mul, id_eq] using hint.trans hmass

end ThreeOmittedValues
