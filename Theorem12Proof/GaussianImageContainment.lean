module

public import Theorem12Proof.GaussianBoundaryGraph
import Mathlib.Tactic

/-!
# The Gaussian image lies above its boundary graph

The perturbation cannot cross its own boundary curve because it is injective
on the closed upper half-plane. A vertical path from each interior point to
large height identifies the upper component.
-/

@[expose] public section

open Complex Metric Set Filter
open scoped Topology

namespace ThreeOmittedValues

theorem gaussianBeta_le_scale_half (x : ℝ) : gaussianBeta x ≤ gaussianScale / 2 := by
  have he : Real.exp (-(gaussianBoundaryHomeomorph.symm x) ^ 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg _))
  unfold gaussianBeta
  nlinarith [gaussianScale_pos]

theorem gaussian_boundary_point (x : ℝ) :
    gaussianPerturbation ((gaussianBoundaryHomeomorph.symm x : ℝ) : ℂ) =
      (x : ℂ) + (gaussianBeta x : ℂ) * Complex.I := by
  let t := gaussianBoundaryHomeomorph.symm x
  have hx : gaussianBoundaryX t = x := by
    rw [← gaussianBoundaryHomeomorph_apply, Homeomorph.apply_symm_apply]
  have hy := gaussianBeta_boundaryX t
  rw [hx] at hy
  apply Complex.ext
  · simpa [gaussianBoundaryX] using hx
  · simpa using hy.symm

theorem gaussianPerturbation_image_above_graph {z : ℂ} (hz : 0 < z.im) :
    gaussianBeta (gaussianPerturbation z).re < (gaussianPerturbation z).im := by
  let ζ : ℝ → ℂ := fun s => (z.re : ℂ) + (s : ℂ) * Complex.I
  have hζ : Continuous ζ := by dsimp [ζ]; fun_prop
  let P : ℝ → ℂ := gaussianPerturbation ∘ ζ
  have hP : Continuous P := gaussianPerturbation_differentiable.continuous.comp hζ
  let L : ℝ → ℝ := fun s => (P s).im - gaussianBeta (P s).re
  have hL : Continuous L := (Complex.continuous_im.comp hP).sub
    (gaussianBeta_continuous.comp (Complex.continuous_re.comp hP))
  have hζz : ζ z.im = z := by
    apply Complex.ext <;> simp [ζ]
  have hPz : P z.im = gaussianPerturbation z := by simp [P, hζz]
  by_contra hnot
  have hlow : L z.im ≤ 0 := by
    dsimp [L]
    rw [hPz]
    linarith
  let b : ℝ := z.im + 2
  have hbim : 0 ≤ (ζ b).im := by simp [ζ, b]; linarith
  have hdisp := gaussianPerturbation_displacement (z := ζ b) hbim
  have hdist := (Complex.abs_im_le_norm (gaussianPerturbation (ζ b) - ζ b)).trans hdisp
  have hdist' := (abs_le.mp hdist).1
  have hbeta := gaussianBeta_le_scale_half (P b).re
  have hhigh : 0 < L b := by
    simp only [Complex.sub_im] at hdist'
    simp only [ζ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, Complex.ofReal_re, mul_one, zero_mul, add_zero, zero_add] at hdist'
    dsimp [L, P, b] at hbeta ⊢
    dsimp [b] at hdist'
    linarith [gaussianScale_le_quarter]
  have hab : z.im ≤ b := by dsimp [b]; linarith
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc hab hL.continuousOn ⟨hlow, hhigh.le⟩
  have hspos : 0 < s := lt_of_lt_of_le hz hs.1
  have hpoint : P s = gaussianPerturbation ((gaussianBoundaryHomeomorph.symm (P s).re : ℝ) : ℂ) := by
    rw [gaussian_boundary_point]
    apply Complex.ext
    · simp
    · have hzero : (P s).im = gaussianBeta (P s).re := by dsimp [L] at hs0; linarith
      simpa using hzero
  have heq : ζ s = ((gaussianBoundaryHomeomorph.symm (P s).re : ℝ) : ℂ) :=
    gaussianPerturbation_injOn (by simp [ζ]; linarith) (by simp) hpoint
  have him := congrArg Complex.im heq
  simp [ζ] at him
  linarith

end ThreeOmittedValues
