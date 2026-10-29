module

public import Theorem12Proof.GaussianPerturbation
public import Theorem12Proof.GaussianBoundary
import Mathlib.Tactic

/-!
# The Gaussian comparison boundary as a graph

The real part of the small perturbation is an increasing homeomorphism of
the real line. Thus the image of the boundary is a positive continuous graph
whose height decays at least as fast as a Gaussian.
-/

@[expose] public section

open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal MeasureTheory ProbabilityTheory Topology

namespace ThreeOmittedValues

noncomputable def gaussianBoundaryX (t : ℝ) : ℝ := (gaussianPerturbation (t : ℂ)).re

theorem gaussianBoundaryX_continuous : Continuous gaussianBoundaryX := by
  exact Complex.continuous_re.comp
    (gaussianPerturbation_differentiable.continuous.comp Complex.continuous_ofReal)

theorem gaussianBoundaryX_close (t : ℝ) : |gaussianBoundaryX t - t| ≤ gaussianScale := by
  have h := (Complex.abs_re_le_norm (gaussianPerturbation (t : ℂ) - (t : ℂ))).trans
    (gaussianPerturbation_displacement (z := (t : ℂ)) (by simp))
  simpa [gaussianBoundaryX] using h

theorem gaussianBoundaryX_strictMono : StrictMono gaussianBoundaryX := by
  intro x y hxy
  have hc := gaussianKernel_lipschitz_upper (z := (y : ℂ)) (w := (x : ℂ)) (by simp) (by simp)
  have hre : |(gaussianKernel (y : ℂ)).re - (gaussianKernel (x : ℂ)).re| ≤
      gaussianMoment * (y - x) := by
    have h := (Complex.abs_re_le_norm (gaussianKernel (y : ℂ) - gaussianKernel (x : ℂ))).trans hc
    simpa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt (sub_pos.mpr hxy))] using h
  have hscaled := mul_le_mul_of_nonneg_left (abs_le.mp hre).1 gaussianScale_pos.le
  have hcoef := mul_le_mul_of_nonneg_right gaussianScale_mul_moment_le_quarter
    (le_of_lt (sub_pos.mpr hxy))
  dsimp [gaussianBoundaryX, gaussianPerturbation]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  nlinarith

theorem gaussianBoundaryX_surjective : Function.Surjective gaussianBoundaryX := by
  intro y
  let a := y - gaussianScale - 1
  let b := y + gaussianScale + 1
  have hab : a ≤ b := by dsimp [a, b]; linarith [gaussianScale_pos]
  have ha : gaussianBoundaryX a ≤ y := by
    have h := (abs_le.mp (gaussianBoundaryX_close a)).2
    dsimp [a] at h
    linarith
  have hb : y ≤ gaussianBoundaryX b := by
    have h := (abs_le.mp (gaussianBoundaryX_close b)).1
    dsimp [b] at h
    linarith
  obtain ⟨t, _ht, hty⟩ := intermediate_value_Icc hab
    gaussianBoundaryX_continuous.continuousOn ⟨ha, hb⟩
  exact ⟨t, hty⟩

noncomputable def gaussianBoundaryHomeomorph : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective gaussianBoundaryX gaussianBoundaryX_strictMono
    gaussianBoundaryX_surjective).toHomeomorph

theorem gaussianBoundaryHomeomorph_apply (t : ℝ) :
    gaussianBoundaryHomeomorph t = gaussianBoundaryX t := rfl

noncomputable def gaussianBeta (x : ℝ) : ℝ :=
  (gaussianScale / 2) * Real.exp (-(gaussianBoundaryHomeomorph.symm x) ^ 2)

theorem gaussianBeta_continuous : Continuous gaussianBeta := by
  unfold gaussianBeta
  fun_prop

theorem gaussianBeta_pos (x : ℝ) : 0 < gaussianBeta x := by
  unfold gaussianBeta
  exact mul_pos (half_pos gaussianScale_pos) (Real.exp_pos _)

theorem gaussianBeta_boundaryX (t : ℝ) :
    gaussianBeta (gaussianBoundaryX t) = (gaussianPerturbation (t : ℂ)).im := by
  have he : gaussianBoundaryHomeomorph.symm (gaussianBoundaryX t) = t := by
    rw [← gaussianBoundaryHomeomorph_apply, Homeomorph.symm_apply_apply]
  simp [gaussianBeta, he, gaussianPerturbation, gaussianKernel_im_real]
  ring

theorem gaussianBeta_upper (x : ℝ) :
    gaussianBeta x ≤ (gaussianScale / 2) * Real.exp (gaussianScale ^ 2) *
      Real.exp (-(x ^ 2) / 2) := by
  let t := gaussianBoundaryHomeomorph.symm x
  have hx : gaussianBoundaryX t = x := by
    rw [← gaussianBoundaryHomeomorph_apply, Homeomorph.apply_symm_apply]
  have hclose := gaussianBoundaryX_close t
  rw [hx] at hclose
  have ht : x ^ 2 / 2 - gaussianScale ^ 2 ≤ t ^ 2 := by
    have ha := (abs_le.mp hclose).1
    have hb := (abs_le.mp hclose).2
    have hsq : (x - t) ^ 2 ≤ gaussianScale ^ 2 := by
      nlinarith [gaussianScale_pos]
    nlinarith [sq_nonneg (x - 2 * t)]
  have hexp : Real.exp (-t ^ 2) ≤
      Real.exp (gaussianScale ^ 2) * Real.exp (-(x ^ 2) / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  change (gaussianScale / 2) * Real.exp (-t ^ 2) ≤ _
  calc
    _ ≤ (gaussianScale / 2) * (Real.exp (gaussianScale ^ 2) *
        Real.exp (-(x ^ 2) / 2)) :=
      mul_le_mul_of_nonneg_left hexp (half_pos gaussianScale_pos).le
    _ = _ := by ring

end ThreeOmittedValues
