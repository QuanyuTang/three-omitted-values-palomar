module

public import Theorem12Proof.GaussianComparisonKernel
import Mathlib.Tactic

/-!
# Gaussian kernel on the real boundary

The symmetric Gaussian characteristic function identifies the imaginary
part of the positive-half kernel as one half of `exp (-x²)`.
-/

@[expose] public section

open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal MeasureTheory ProbabilityTheory Topology

namespace ThreeOmittedValues

theorem gaussian_cos_integrable (x : ℝ) :
    Integrable (fun u : ℝ => Real.cos (x * u)) (gaussianReal 0 (2 : ℝ≥0)) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards with u
  simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (x * u)

theorem gaussian_cos_even_split (x : ℝ) :
    2 * (∫ u : ℝ in Ioi 0, Real.cos (x * u) ∂gaussianReal 0 (2 : ℝ≥0)) =
      ∫ u : ℝ, Real.cos (x * u) ∂gaussianReal 0 (2 : ℝ≥0) := by
  let μ := gaussianReal 0 (2 : ℝ≥0)
  letI : NullSingletonClass μ := nullSingletonClass_gaussianReal (by norm_num)
  have hneg : μ.map (fun u : ℝ => -u) = μ := by
    simpa [μ] using (gaussianReal_map_neg (μ := 0) (v := (2 : ℝ≥0)))
  have hemb : MeasurableEmbedding (fun u : ℝ => -u) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hmap := hemb.setIntegral_map (μ := μ) (fun u : ℝ => Real.cos (x * u)) (Iio 0)
  rw [hneg] at hmap
  have hhalf : (∫ u : ℝ in Iio 0, Real.cos (x * u) ∂μ) =
      ∫ u : ℝ in Ioi 0, Real.cos (x * u) ∂μ := by
    simpa only [neg_preimage, neg_Iio, neg_zero, mul_neg, Real.cos_neg] using hmap
  have hsplit := integral_add_compl (μ := μ) (s := Ioi (0 : ℝ))
    (f := fun u : ℝ => Real.cos (x * u))
    measurableSet_Ioi (gaussian_cos_integrable x)
  rw [compl_Ioi, integral_Iic_eq_integral_Iio, hhalf] at hsplit
  linarith

theorem gaussian_cos_integral (x : ℝ) :
    (∫ u : ℝ, Real.cos (x * u) ∂gaussianReal 0 (2 : ℝ≥0)) = Real.exp (-x ^ 2) := by
  let μ := gaussianReal 0 (2 : ℝ≥0)
  have hint : Integrable (fun u : ℝ => Complex.exp ((Complex.I * (x : ℂ)) * u)) μ := by
    apply integrable_cexp_mul_of_re_mem_integrableExpSet (X := id) (by fun_prop)
    simp [μ, integrableExpSet_id_gaussianReal]
  have hmgf := complexMGF_id_gaussianReal (μ := 0) (v := (2 : ℝ≥0))
    (Complex.I * (x : ℂ))
  have hre := congrArg Complex.re hmgf
  rw [complexMGF] at hre
  change (∫ u : ℝ, Complex.exp ((Complex.I * (x : ℂ)) * u) ∂μ).re = _ at hre
  have hreal : (∫ u : ℝ, Complex.exp ((Complex.I * (x : ℂ)) * u) ∂μ).re =
      ∫ u : ℝ, (Complex.exp ((Complex.I * (x : ℂ)) * u)).re ∂μ := by
    simpa only using! (integral_re hint).symm
  rw [hreal] at hre
  have hpow : (Complex.I * (x : ℂ)) ^ 2 = ((-x ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  have harg : Complex.I * (x : ℂ) * ((0 : ℝ) : ℂ) +
      (((2 : ℝ≥0) : ℝ) : ℂ) * (Complex.I * (x : ℂ)) ^ 2 / 2 =
      ((-x ^ 2 : ℝ) : ℂ) := by
    norm_num
    rw [hpow]
    push_cast
    ring
  rw [harg] at hre
  simpa [μ, Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, pow_two] using hre

theorem gaussianKernel_im_real (x : ℝ) :
    (gaussianKernel (x : ℂ)).im = (1 / 2 : ℝ) * Real.exp (-x ^ 2) := by
  have hint : Integrable (fun u : ℝ => Complex.exp ((Complex.I * (x : ℂ)) * u))
      positiveGaussian := by
    apply integrable_cexp_mul_of_re_mem_integrableExpSet (X := id) (by fun_prop)
    simp [positiveGaussian_expSet]
  have hre : (∫ u : ℝ, Complex.exp ((Complex.I * (x : ℂ)) * u) ∂positiveGaussian).re =
      ∫ u : ℝ, (Complex.exp ((Complex.I * (x : ℂ)) * u)).re ∂positiveGaussian := by
    simpa only using! (integral_re hint).symm
  have hsplit := gaussian_cos_even_split x
  rw [gaussian_cos_integral] at hsplit
  unfold gaussianKernel complexMGF
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, id_eq]
  rw [hre]
  simp only [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add, sub_zero,
    mul_zero, Real.exp_zero, one_mul]
  change (∫ u : ℝ in Ioi 0, Real.cos (x * u) ∂gaussianReal 0 (2 : ℝ≥0)) = _
  linarith

end ThreeOmittedValues
