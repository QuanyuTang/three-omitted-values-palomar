module

public import Theorem12Proof.ModularCuspLimits
import Mathlib.Tactic

/-!
# Three explicit families of modular cusps

Even integers, odd integers, and even-integer translates of one half give
the three different cusps of the modular lambda function.
-/

@[expose] public section

open Complex UpperHalfPlane NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold

namespace ThreeOmittedValues

noncomputable def evenCuspShift (n : ℤ) : SL(2, ℤ) := ModularGroup.T ^ (2 * n)

noncomputable def zeroCuspBase : SL(2, ℤ) :=
  (-1 : SL(2, ℤ)) * (ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) * ModularGroup.S)

noncomputable def zeroCuspMatrix (n : ℤ) : SL(2, ℤ) := evenCuspShift n * zeroCuspBase
noncomputable def oneCuspMatrix (n : ℤ) : SL(2, ℤ) := evenCuspShift n * ModularGroup.S
noncomputable def poleCuspMatrix (n : ℤ) : SL(2, ℤ) :=
  evenCuspShift n * (ModularGroup.T * ModularGroup.S)

theorem evenCuspShift_mem_gamma_two (n : ℤ) : evenCuspShift n ∈ CongruenceSubgroup.Gamma 2 := by
  rw [evenCuspShift, zpow_mul]
  exact Subgroup.zpow_mem _ T_sq_mem_gamma_two n

theorem zeroCuspBase_mem_gamma_two : zeroCuspBase ∈ CongruenceSubgroup.Gamma 2 :=
  Subgroup.mul_mem _ neg_one_mem_gamma_two S_T_neg_two_S_mem_gamma_two

theorem zeroCuspMatrix_formula (n : ℤ) (τ : UpperHalfPlane) :
    modularLambdaH ((zeroCuspMatrix n • τ : UpperHalfPlane) : ℂ) =
      lambdaTransform 0 (modularLambdaH (τ : ℂ)) := by
  have h := Subgroup.mul_mem (CongruenceSubgroup.Gamma 2)
    (evenCuspShift_mem_gamma_two n) zeroCuspBase_mem_gamma_two
  simpa [zeroCuspMatrix, lambdaTransform] using modularLambdaH_gamma2_invariant _ h τ

theorem oneCuspMatrix_formula (n : ℤ) (τ : UpperHalfPlane) :
    modularLambdaH ((oneCuspMatrix n • τ : UpperHalfPlane) : ℂ) =
      lambdaTransform 1 (modularLambdaH (τ : ℂ)) := by
  rw [oneCuspMatrix, mul_smul,
    modularLambdaH_gamma2_invariant _ (evenCuspShift_mem_gamma_two n), modularLambdaH_S_formula]
  rfl

theorem poleCuspMatrix_formula (n : ℤ) (τ : UpperHalfPlane) :
    modularLambdaH ((poleCuspMatrix n • τ : UpperHalfPlane) : ℂ) =
      lambdaTransform 4 (modularLambdaH (τ : ℂ)) := by
  rw [poleCuspMatrix, mul_smul,
    modularLambdaH_gamma2_invariant _ (evenCuspShift_mem_gamma_two n), modularLambdaH_TS_formula]
  rfl

theorem oneCuspMatrix_first_column (n : ℤ) :
    (oneCuspMatrix n).val 0 0 = 2 * n ∧ (oneCuspMatrix n).val 1 0 = 1 := by
  constructor <;> change ((evenCuspShift n * ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) _ _ = _
  all_goals rw [Matrix.SpecialLinearGroup.coe_mul, evenCuspShift, ModularGroup.coe_T_zpow, ModularGroup.coe_S]
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem poleCuspMatrix_first_column (n : ℤ) :
    (poleCuspMatrix n).val 0 0 = 2 * n + 1 ∧ (poleCuspMatrix n).val 1 0 = 1 := by
  constructor <;> change ((evenCuspShift n * (ModularGroup.T * ModularGroup.S) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) _ _ = _
  all_goals rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    evenCuspShift, ModularGroup.coe_T_zpow, ModularGroup.coe_T, ModularGroup.coe_S]
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem zeroCuspMatrix_first_column (n : ℤ) :
    (zeroCuspMatrix n).val 0 0 = 4 * n + 1 ∧ (zeroCuspMatrix n).val 1 0 = 2 := by
  have hU : ((zeroCuspBase : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 2, 1] := by
    ext i j
    exact U_matrix_val i j
  constructor <;> change ((evenCuspShift n * zeroCuspBase : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) _ _ = _
  all_goals rw [Matrix.SpecialLinearGroup.coe_mul, evenCuspShift, ModularGroup.coe_T_zpow, hU]
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end ThreeOmittedValues
