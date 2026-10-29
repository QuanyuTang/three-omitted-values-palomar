module

public import Theorem12Proof.ModularRealTransforms
import Mathlib.Tactic

/-!
# The six rational transformations of modular lambda

For a fixed element of `SL₂(ℤ)`, one of six explicit rational functions
describes its action on lambda at every upper-half-plane point. This is the
input for classifying finite rational cusp values.
-/

@[expose] public section

open Complex UpperHalfPlane NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold

namespace ThreeOmittedValues

noncomputable def lambdaTransform (k : Fin 6) (z : ℂ) : ℂ :=
  ![z, 1 - z, z / (z - 1), 1 / (1 - z), (z - 1) / z, 1 / z] k

theorem modularLambdaH_ST_formula (τ : UpperHalfPlane) :
    modularLambdaH (((ModularGroup.S * ModularGroup.T) • τ : UpperHalfPlane) : ℂ) =
      1 / (1 - modularLambdaH (τ : ℂ)) := by
  rw [mul_smul, modularLambdaH_S_formula, modularLambdaH_T_formula]
  have h1 := modularLambdaH_ne_one (show 0 < (τ : ℂ).im from τ.im_pos)
  have hn : modularLambdaH (τ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hn' : 1 - modularLambdaH (τ : ℂ) ≠ 0 := sub_ne_zero.mpr h1.symm
  field_simp
  ring

theorem modularLambdaH_TS_formula (τ : UpperHalfPlane) :
    modularLambdaH (((ModularGroup.T * ModularGroup.S) • τ : UpperHalfPlane) : ℂ) =
      (modularLambdaH (τ : ℂ) - 1) / modularLambdaH (τ : ℂ) := by
  rw [mul_smul, modularLambdaH_T_formula, modularLambdaH_S_formula]
  have h0 := modularLambdaH_ne_zero (show 0 < (τ : ℂ).im from τ.im_pos)
  have heq : 1 - modularLambdaH (τ : ℂ) - 1 = -modularLambdaH (τ : ℂ) := by ring
  rw [heq]
  field_simp [h0]
  ring

theorem modularLambdaH_STS_formula (τ : UpperHalfPlane) :
    modularLambdaH (((ModularGroup.S * ModularGroup.T * ModularGroup.S) • τ : UpperHalfPlane) : ℂ) =
      1 / modularLambdaH (τ : ℂ) := by
  rw [mul_smul, mul_smul, modularLambdaH_S_formula, modularLambdaH_T_formula,
    modularLambdaH_S_formula]
  have h0 := modularLambdaH_ne_zero (show 0 < (τ : ℂ).im from τ.im_pos)
  have heq : 1 - modularLambdaH (τ : ℂ) - 1 = -modularLambdaH (τ : ℂ) := by ring
  rw [heq]
  field_simp [h0]
  ring

theorem modularLambdaH_six_transforms (γ : SL(2, ℤ)) :
    ∃ k : Fin 6, ∀ τ : UpperHalfPlane,
      modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ) = lambdaTransform k (modularLambdaH (τ : ℂ)) := by
  rcases reduceModTwo_enumeration (reduceModTwo γ) with h | h | h | h | h | h
  · refine ⟨0, fun τ => ?_⟩
    simpa [lambdaTransform] using modularLambdaH_same_mod_two γ 1 h τ
  · refine ⟨1, fun τ => ?_⟩
    rw [modularLambdaH_same_mod_two γ ModularGroup.S h τ, modularLambdaH_S_formula]
    rfl
  · refine ⟨2, fun τ => ?_⟩
    rw [modularLambdaH_same_mod_two γ ModularGroup.T h τ, modularLambdaH_T_formula]
    rfl
  · refine ⟨3, fun τ => ?_⟩
    rw [modularLambdaH_same_mod_two γ (ModularGroup.S * ModularGroup.T) h τ,
      modularLambdaH_ST_formula]
    rfl
  · refine ⟨4, fun τ => ?_⟩
    rw [modularLambdaH_same_mod_two γ (ModularGroup.T * ModularGroup.S) h τ,
      modularLambdaH_TS_formula]
    rfl
  · refine ⟨5, fun τ => ?_⟩
    rw [modularLambdaH_same_mod_two γ (ModularGroup.S * ModularGroup.T * ModularGroup.S) h τ,
      modularLambdaH_STS_formula]
    rfl

end ThreeOmittedValues
