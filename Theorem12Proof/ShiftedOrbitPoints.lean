module

public import Theorem12Proof.SelectedOrbitPoints
import Mathlib.Tactic

/-!
# Even translations of selected modular orbit points

The translation may depend on the level. It leaves the lower matrix row and
the imaginary part unchanged, so injectivity remains valid even when different
levels use different shifts.
-/

@[expose] public section

open Complex UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

namespace ThreeOmittedValues

noncomputable def shiftedOrbitMatrix (N : ℕ) (hN : 2 ≤ N) (k : ℕ → ℤ)
    (i : OrbitIndexFrom N) : SL(2, ℤ) :=
  ModularGroup.T ^ (2 * k i.1.1) * orbitMatrix N hN i

theorem shiftedOrbitMatrix_mem (N : ℕ) (hN : 2 ≤ N) (k : ℕ → ℤ)
    (i : OrbitIndexFrom N) : shiftedOrbitMatrix N hN k i ∈ CongruenceSubgroup.Gamma 2 := by
  apply (CongruenceSubgroup.Gamma 2).mul_mem
  · have h := CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma 2 (2 * k i.1.1)
      (dvd_mul_right 2 (k i.1.1))
    simpa using h
  · exact orbitMatrix_mem_gamma_two N hN i

theorem shiftedOrbitMatrix_lower_left (N : ℕ) (hN : 2 ≤ N) (k : ℕ → ℤ)
    (i : OrbitIndexFrom N) :
    (shiftedOrbitMatrix N hN k i : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 2 * (i.1.1 : ℤ) := by
  simp [shiftedOrbitMatrix, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
    Matrix.mul_apply, Fin.sum_univ_two, orbitMatrix_lower_left]

theorem shiftedOrbitMatrix_lower_right (N : ℕ) (hN : 2 ≤ N) (k : ℕ → ℤ)
    (i : OrbitIndexFrom N) :
    (shiftedOrbitMatrix N hN k i : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (i.2.1 : ℤ) := by
  simp [shiftedOrbitMatrix, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
    Matrix.mul_apply, Fin.sum_univ_two, orbitMatrix_lower_right]

noncomputable def shiftedOrbitPoint (N : ℕ) (hN : 2 ≤ N) (k : ℕ → ℤ)
    (τ : UpperHalfPlane) (i : OrbitIndexFrom N) : ℂ :=
  ((shiftedOrbitMatrix N hN k i • τ : UpperHalfPlane) : ℂ)

theorem shiftedOrbitPoint_eq (N : ℕ) (hN : 2 ≤ N) (k : ℕ → ℤ)
    (τ : UpperHalfPlane) (i : OrbitIndexFrom N) :
    shiftedOrbitPoint N hN k τ i = orbitPoint N hN τ i + (2 * k i.1.1 : ℤ) := by
  simp only [shiftedOrbitPoint, shiftedOrbitMatrix, mul_smul, ModularGroup.coe_T_zpow_smul_eq,
    orbitPoint]

theorem shiftedOrbitPoint_im (N : ℕ) (hN : 2 ≤ N) (k : ℕ → ℤ)
    (τ : UpperHalfPlane) (i : OrbitIndexFrom N) :
    (shiftedOrbitPoint N hN k τ i).im = (orbitPoint N hN τ i).im := by
  simp [shiftedOrbitPoint_eq]

theorem shiftedOrbitPoint_lambda (N : ℕ) (hN : 2 ≤ N) (k : ℕ → ℤ)
    (τ : UpperHalfPlane) (i : OrbitIndexFrom N) :
    NoWanderingDomains.modularLambdaH (shiftedOrbitPoint N hN k τ i) =
      NoWanderingDomains.modularLambdaH (τ : ℂ) :=
  NoWanderingDomains.modularLambdaH_gamma2_invariant _ (shiftedOrbitMatrix_mem N hN k i) τ

theorem shiftedOrbitPoint_injective (N : ℕ) (hN : 2 ≤ N) (k : ℕ → ℤ)
    (τ : UpperHalfPlane) : Function.Injective (shiftedOrbitPoint N hN k τ) := by
  intro i j hij
  have hmi : 0 < (shiftedOrbitMatrix N hN k i : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rw [shiftedOrbitMatrix_lower_left]
    have := i.1.2
    exact_mod_cast (show 0 < 2 * i.1.1 by omega)
  have hmj : 0 < (shiftedOrbitMatrix N hN k j : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rw [shiftedOrbitMatrix_lower_left]
    have := j.1.2
    exact_mod_cast (show 0 < 2 * j.1.1 by omega)
  have hmatrix : shiftedOrbitMatrix N hN k i = shiftedOrbitMatrix N hN k j :=
    gamma_two_orbit_injective_of_positive_lower_left _ _
      (shiftedOrbitMatrix_mem N hN k i) (shiftedOrbitMatrix_mem N hN k j)
      hmi hmj τ (UpperHalfPlane.ext hij)
  have hmval : i.1.1 = j.1.1 := by
    have h := congrArg (fun γ : SL(2, ℤ) => (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) hmatrix
    rw [shiftedOrbitMatrix_lower_left, shiftedOrbitMatrix_lower_left] at h
    have h' : 2 * i.1.1 = 2 * j.1.1 := by exact_mod_cast h
    omega
  have hdval : i.2.1 = j.2.1 := by
    have h := congrArg (fun γ : SL(2, ℤ) => (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) hmatrix
    rw [shiftedOrbitMatrix_lower_right, shiftedOrbitMatrix_lower_right] at h
    exact_mod_cast h
  cases i with
  | mk mi di =>
    cases j with
    | mk mj dj =>
      have hm : mi = mj := Subtype.ext hmval
      subst mj
      have hd : di = dj := Subtype.ext hdval
      subst dj
      rfl

end ThreeOmittedValues
