module

public import Theorem12Proof.ModTwoCosets
public import Theorem12Proof.NoWanderingDomains.Hyperbolic.ModularCoveringMap.WindingInjectivity
import Mathlib.Tactic

/-!
# Real values under modular transformations

The modular lambda function's `S` and `T` formulas preserve real values.
The six cosets modulo `Γ(2)` then show that every element of `SL₂(ℤ)`
preserves the property of taking a real value.
-/

@[expose] public section

open Complex UpperHalfPlane NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold

namespace ThreeOmittedValues

theorem modularLambdaH_S_formula (τ : UpperHalfPlane) :
    modularLambdaH ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
      1 - modularLambdaH (τ : ℂ) := by
  have h := modularLambdaH_add_S_smul_eq_one (show 0 < (τ : ℂ).im from τ.im_pos)
  have heq : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
    simp only [inv_neg, neg_div, one_div]
  rw [heq]
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)

theorem modularLambdaH_T_formula (τ : UpperHalfPlane) :
    modularLambdaH ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) =
      modularLambdaH (τ : ℂ) / (modularLambdaH (τ : ℂ) - 1) := by
  have hτ : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    have h := ModularGroup.coe_T_zpow_smul_eq (z := τ) (n := 1)
    simpa using h
  rw [hτ]
  exact modularLambdaH_T_smul_div (show 0 < (τ : ℂ).im from τ.im_pos)

theorem modularLambdaH_S_real (τ : UpperHalfPlane) (hτ : (modularLambdaH (τ : ℂ)).im = 0) :
    (modularLambdaH ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)).im = 0 := by
  rw [modularLambdaH_S_formula]
  simp [hτ]

theorem modularLambdaH_T_real (τ : UpperHalfPlane) (hτ : (modularLambdaH (τ : ℂ)).im = 0) :
    (modularLambdaH ((ModularGroup.T • τ : UpperHalfPlane) : ℂ)).im = 0 := by
  rw [modularLambdaH_T_formula]
  simp [Complex.div_im, Complex.sub_im, hτ]

theorem modularLambdaH_SL2_real (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (hτ : (modularLambdaH (τ : ℂ)).im = 0) :
    (modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ)).im = 0 := by
  rcases reduceModTwo_enumeration (reduceModTwo γ) with h | h | h | h | h | h
  · rw [modularLambdaH_same_mod_two γ 1 h τ]
    simpa using hτ
  · rw [modularLambdaH_same_mod_two γ ModularGroup.S h τ]
    exact modularLambdaH_S_real τ hτ
  · rw [modularLambdaH_same_mod_two γ ModularGroup.T h τ]
    exact modularLambdaH_T_real τ hτ
  · rw [modularLambdaH_same_mod_two γ (ModularGroup.S * ModularGroup.T) h τ, mul_smul]
    exact modularLambdaH_S_real _ (modularLambdaH_T_real τ hτ)
  · rw [modularLambdaH_same_mod_two γ (ModularGroup.T * ModularGroup.S) h τ, mul_smul]
    exact modularLambdaH_T_real _ (modularLambdaH_S_real τ hτ)
  · rw [modularLambdaH_same_mod_two γ (ModularGroup.S * ModularGroup.T * ModularGroup.S) h τ,
      mul_smul, mul_smul]
    exact modularLambdaH_S_real _ (modularLambdaH_T_real _ (modularLambdaH_S_real τ hτ))

end ThreeOmittedValues
