module

public import Theorem12Proof.NoWanderingDomains.Hyperbolic.ModularFunction.GammaTwoInvariance
import Mathlib.Tactic

/-!
# Distinct positive-denominator matrices have distinct orbit points

The action of `Γ(2)` on the upper half-plane is free modulo `±I`. If both
matrices have positive lower-left entry, the negative ambiguity disappears.
-/

@[expose] public section

open Complex UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

namespace ThreeOmittedValues

theorem gamma_two_orbit_injective_of_positive_lower_left
    (γ₁ γ₂ : SL(2, ℤ)) (hγ₁ : γ₁ ∈ CongruenceSubgroup.Gamma 2)
    (hγ₂ : γ₂ ∈ CongruenceSubgroup.Gamma 2)
    (hc₁ : 0 < (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (hc₂ : 0 < (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (τ : UpperHalfPlane) (heq : γ₁ • τ = γ₂ • τ) : γ₁ = γ₂ := by
  let δ : SL(2, ℤ) := γ₁⁻¹ * γ₂
  have hδ : δ ∈ CongruenceSubgroup.Gamma 2 :=
    (CongruenceSubgroup.Gamma 2).mul_mem ((CongruenceSubgroup.Gamma 2).inv_mem hγ₁) hγ₂
  have hfix : δ • τ = τ := by
    calc
      δ • τ = γ₁⁻¹ • (γ₂ • τ) := by simp [δ, mul_smul]
      _ = γ₁⁻¹ • (γ₁ • τ) := by rw [heq]
      _ = τ := inv_smul_smul γ₁ τ
  have hγ₂eq : γ₂ = γ₁ * δ := by simp [δ, mul_assoc]
  rcases NoWanderingDomains.gamma_two_fixed_point_implies_pm_one δ hδ τ hfix with hδone | hδneg
  · have h : γ₂ = γ₁ := by simpa only [hδone, mul_one] using hγ₂eq
    exact h.symm
  · have h : γ₂ = -γ₁ := by simpa only [hδneg, mul_neg_one] using hγ₂eq
    have hc : (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
        -((γ₁ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
      have hv := congrArg (fun γ : SL(2, ℤ) => (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) h
      simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] using hv
    linarith

end ThreeOmittedValues
