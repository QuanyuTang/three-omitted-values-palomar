module

public import Theorem12Proof.FareyCuspGeometry
public import Theorem12Proof.FareyVertexMatrix
import Mathlib.Tactic

/-!
# Möbius height at a Farey vertex

For a modular matrix with first column `(p,q)`, its inverse sends the cusp
`p/q` to infinity. The graph estimate proves that its imaginary part tends
to infinity along every approach from within the Farey domain.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set Filter NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold Topology

namespace ThreeOmittedValues

theorem inverse_modular_im_formula (γ : SL(2, ℤ)) (p q : ℤ) (hq : 0 < q)
    (h00 : γ.val 0 0 = p) (h10 : γ.val 1 0 = q) (τ : UpperHalfPlane) :
    (((γ⁻¹ • τ : UpperHalfPlane) : ℂ)).im =
      ((τ : ℂ).im / (((τ : ℂ).re - (p : ℝ) / (q : ℝ)) ^ 2 + (τ : ℂ).im ^ 2)) /
        (q : ℝ) ^ 2 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hinv10 : (γ⁻¹).val 1 0 = -q := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [h10]
  have hinv11 : (γ⁻¹).val 1 1 = p := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [h00]
  have h := ModularGroup.im_smul_eq_div_normSq (γ⁻¹) τ
  rw [ModularGroup.denom_apply, hinv10, hinv11] at h
  have hnorm : Complex.normSq ((-(q : ℂ)) * (τ : ℂ) + (p : ℂ)) =
      (q : ℝ) ^ 2 * (((τ : ℂ).re - (p : ℝ) / (q : ℝ)) ^ 2 + (τ : ℂ).im ^ 2) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.intCast_re, Complex.intCast_im,
      neg_zero, zero_mul, mul_zero, sub_zero, add_zero]
    field_simp
    ring
  simp only [Int.cast_neg, Complex.ofReal_neg, hnorm] at h
  calc
    (((γ⁻¹ • τ : UpperHalfPlane) : ℂ)).im =
        (τ : ℂ).im / ((q : ℝ) ^ 2 *
          (((τ : ℂ).re - (p : ℝ) / (q : ℝ)) ^ 2 + (τ : ℂ).im ^ 2)) := by
      simpa only [UpperHalfPlane.coe_im] using h
    _ = _ := by
      rw [div_mul_eq_div_div]
      simp only [div_eq_mul_inv]
      ring

theorem farey_vertex_inverse_height_closed_tendsto {α : Type*} {l : Filter α}
    (levels : ℤ → ℕ) (r : ℝ) (hr0 : pastedFareyHeight levels r = 0)
    (γ : SL(2, ℤ)) (p q : ℤ) (hq : 0 < q)
    (hr : r = (p : ℝ) / (q : ℝ)) (h00 : γ.val 0 0 = p) (h10 : γ.val 1 0 = q)
    (T : α → UpperHalfPlane) (hT : Tendsto (fun a => (T a : ℂ)) l (𝓝 (r : ℂ)))
    (hdom : ∀ᶠ a in l, pastedFareyHeight levels (T a : ℂ).re ≤ (T a : ℂ).im) :
    Tendsto (fun a => (((γ⁻¹ • T a : UpperHalfPlane) : ℂ)).im) l atTop := by
  have hdom' : ∀ᶠ a in l, pastedFareyHeight levels (T a : ℂ).re ≤ (T a : ℂ).im ∧
      0 < (T a : ℂ).im := by
    filter_upwards [hdom] with a ha
    exact ⟨ha, (T a).im_pos⟩
  have hratio := farey_vertex_ratio_closed_tendsto_atTop levels r hr0 (fun a => (T a : ℂ)) hT hdom'
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htop := hratio.atTop_div_const (show 0 < (q : ℝ) ^ 2 by positivity)
  have heq : (fun a => (((γ⁻¹ • T a : UpperHalfPlane) : ℂ)).im) =
      (fun a => ((T a : ℂ).im / (((T a : ℂ).re - r) ^ 2 + (T a : ℂ).im ^ 2)) /
        (q : ℝ) ^ 2) := by
    funext a
    rw [inverse_modular_im_formula γ p q hq h00 h10, hr]
  rw [heq]
  exact htop

theorem farey_vertex_inverse_height_tendsto {α : Type*} {l : Filter α}
    (levels : ℤ → ℕ) (r : ℝ) (hr0 : pastedFareyHeight levels r = 0)
    (γ : SL(2, ℤ)) (p q : ℤ) (hq : 0 < q)
    (hr : r = (p : ℝ) / (q : ℝ)) (h00 : γ.val 0 0 = p) (h10 : γ.val 1 0 = q)
    (T : α → UpperHalfPlane) (hT : Tendsto (fun a => (T a : ℂ)) l (𝓝 (r : ℂ)))
    (hdom : ∀ᶠ a in l, (T a : ℂ) ∈ upperGraphDomain (pastedFareyHeight levels)) :
    Tendsto (fun a => (((γ⁻¹ • T a : UpperHalfPlane) : ℂ)).im) l atTop := by
  apply farey_vertex_inverse_height_closed_tendsto levels r hr0 γ p q hq hr h00 h10 T hT
  filter_upwards [hdom] with a ha
  exact ha.le

end ThreeOmittedValues
