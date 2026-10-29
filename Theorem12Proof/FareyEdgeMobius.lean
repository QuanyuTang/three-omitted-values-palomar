module

public import Theorem12Proof.ModularRealTransforms
import Mathlib.Tactic

/-!
# Real modular-lambda values on determinant-one semicircles

Every such semicircle is the image of the imaginary axis under an integral
determinant-one Möbius transformation. The modular transformation result
therefore makes lambda real on the entire open semicircle.
-/

@[expose] public section

open Complex UpperHalfPlane NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold

namespace ThreeOmittedValues

def fareyEdgeMatrix (a b c d : ℤ) (hdet : c * b - a * d = 1) : SL(2, ℤ) :=
  ⟨!![c, a; d, b], by simpa [Matrix.det_fin_two_of] using hdet⟩

theorem fareyEdge_inverse_real_part_zero (a b c d : ℤ) (hdet : c * b - a * d = 1)
    (τ : UpperHalfPlane)
    (hcircle : ((b : ℝ) * (τ : ℂ).re - a) * ((c : ℝ) - (d : ℝ) * (τ : ℂ).re) =
      ((b : ℝ) * (d : ℝ)) * (τ : ℂ).im ^ 2) :
    (((fareyEdgeMatrix a b c d hdet)⁻¹ • τ : UpperHalfPlane) : ℂ).re = 0 := by
  have hinv : ((fareyEdgeMatrix a b c d hdet)⁻¹).val =
      !![b, -a; -d, c] := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    simp [fareyEdgeMatrix, Matrix.adjugate_fin_two]
  have h00 : ((fareyEdgeMatrix a b c d hdet)⁻¹).val 0 0 = b := by rw [hinv]; simp
  have h01 : ((fareyEdgeMatrix a b c d hdet)⁻¹).val 0 1 = -a := by rw [hinv]; simp
  have h10 : ((fareyEdgeMatrix a b c d hdet)⁻¹).val 1 0 = -d := by rw [hinv]; simp
  have h11 : ((fareyEdgeMatrix a b c d hdet)⁻¹).val 1 1 = c := by rw [hinv]; simp
  have hform : (((fareyEdgeMatrix a b c d hdet)⁻¹ • τ : UpperHalfPlane) : ℂ) =
      ((b : ℂ) * (τ : ℂ) - a) / (-(d : ℂ) * (τ : ℂ) + c) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [h00, h01, h10, h11, sub_eq_add_neg]
  rw [hform]
  simp only [Complex.div_re, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.intCast_re,
    Complex.intCast_im, neg_zero, zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  have hnum : ((b : ℝ) * (τ : ℂ).re - a) *
      (-(d : ℝ) * (τ : ℂ).re + c) +
      ((b : ℝ) * (τ : ℂ).im) * (-(d : ℝ) * (τ : ℂ).im) = 0 := by
    nlinarith [hcircle]
  rw [← add_div, hnum, zero_div]

theorem modularLambdaH_real_on_farey_semicircle
    (a b c d : ℤ) (hdet : c * b - a * d = 1) (τ : UpperHalfPlane)
    (hcircle : ((b : ℝ) * (τ : ℂ).re - a) * ((c : ℝ) - (d : ℝ) * (τ : ℂ).re) =
      ((b : ℝ) * (d : ℝ)) * (τ : ℂ).im ^ 2) :
    (modularLambdaH (τ : ℂ)).im = 0 := by
  let γ := fareyEdgeMatrix a b c d hdet
  let σ : UpperHalfPlane := γ⁻¹ • τ
  have hre : (σ : ℂ).re = 0 := fareyEdge_inverse_real_part_zero a b c d hdet τ hcircle
  have hrepr : (σ : ℂ) = ((σ : ℂ).im : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero] using! hre
    · simp
  have hσ : (modularLambdaH (σ : ℂ)).im = 0 := by
    have hrepr' : (σ : ℂ) = Complex.I * ((σ : ℂ).im : ℂ) := by
      exact hrepr.trans (mul_comm _ _)
    have hh := modularLambdaH_pure_imag_real (show 0 < (σ : ℂ).im from σ.im_pos)
    rw [hrepr']
    exact hh
  have hreal := modularLambdaH_SL2_real γ σ hσ
  have hγσ : γ • σ = τ := smul_inv_smul γ τ
  simpa only [hγσ] using hreal

end ThreeOmittedValues
