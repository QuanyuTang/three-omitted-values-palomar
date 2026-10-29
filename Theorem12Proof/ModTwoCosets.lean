module

public import Theorem12Proof.GammaOrbitInjectivity
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

/-!
# Cosets modulo the level-two subgroup

The six cosets are represented by `1`, `S`, `T`, `ST`, `TS`, `STS`.
These representatives account for the six fractional-linear transformations
of the modular lambda function.
-/

@[expose] public section

open scoped MatrixGroups ModularForm Manifold

namespace ThreeOmittedValues

noncomputable def reduceModTwo : SL(2, ℤ) →* SL(2, ZMod 2) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2))

theorem reduceModTwo_enumeration : ∀ g : SL(2, ZMod 2),
    g = reduceModTwo 1 ∨ g = reduceModTwo ModularGroup.S ∨
    g = reduceModTwo ModularGroup.T ∨ g = reduceModTwo (ModularGroup.S * ModularGroup.T) ∨
    g = reduceModTwo (ModularGroup.T * ModularGroup.S) ∨
    g = reduceModTwo (ModularGroup.S * ModularGroup.T * ModularGroup.S) := by
  decide

theorem gamma_two_of_same_reduction (γ ρ : SL(2, ℤ))
    (h : reduceModTwo γ = reduceModTwo ρ) :
    γ * ρ⁻¹ ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem']
  change reduceModTwo (γ * ρ⁻¹) = 1
  rw [map_mul, map_inv, h, mul_inv_cancel]

theorem modularLambdaH_same_mod_two (γ ρ : SL(2, ℤ))
    (h : reduceModTwo γ = reduceModTwo ρ) (τ : UpperHalfPlane) :
    NoWanderingDomains.modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ) =
      NoWanderingDomains.modularLambdaH ((ρ • τ : UpperHalfPlane) : ℂ) := by
  let δ := γ * ρ⁻¹
  have hδ : δ ∈ CongruenceSubgroup.Gamma 2 := gamma_two_of_same_reduction γ ρ h
  have hmul : δ * ρ = γ := by simp [δ, mul_assoc]
  have hlambda := NoWanderingDomains.modularLambdaH_gamma2_invariant δ hδ (ρ • τ)
  rw [← mul_smul, hmul] at hlambda
  exact hlambda

theorem exists_six_coset_representative (γ : SL(2, ℤ)) :
    ∃ ρ : SL(2, ℤ),
      (ρ = 1 ∨ ρ = ModularGroup.S ∨ ρ = ModularGroup.T ∨
        ρ = ModularGroup.S * ModularGroup.T ∨ ρ = ModularGroup.T * ModularGroup.S ∨
        ρ = ModularGroup.S * ModularGroup.T * ModularGroup.S) ∧
      γ * ρ⁻¹ ∈ CongruenceSubgroup.Gamma 2 := by
  rcases reduceModTwo_enumeration (reduceModTwo γ) with h | h | h | h | h | h
  · exact ⟨1, Or.inl rfl, gamma_two_of_same_reduction γ 1 h⟩
  · exact ⟨ModularGroup.S, Or.inr (Or.inl rfl), gamma_two_of_same_reduction γ _ h⟩
  · exact ⟨ModularGroup.T, Or.inr (Or.inr (Or.inl rfl)), gamma_two_of_same_reduction γ _ h⟩
  · exact ⟨ModularGroup.S * ModularGroup.T, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
      gamma_two_of_same_reduction γ _ h⟩
  · exact ⟨ModularGroup.T * ModularGroup.S, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      gamma_two_of_same_reduction γ _ h⟩
  · exact ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), gamma_two_of_same_reduction γ _ h⟩

end ThreeOmittedValues
