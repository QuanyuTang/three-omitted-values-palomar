module

public import Theorem12Proof.LogarithmicOrbitShift
public import Theorem12Proof.GaussianComparisonDomain
import Mathlib.Tactic

/-!
# Quantitative geometry of the shifted orbit

At sufficiently large levels the shifted points lie above the Gaussian
boundary, while their horizontal square grows at most logarithmically.
-/

@[expose] public section

open Complex UpperHalfPlane CongruenceSubgroup Set
open scoped ModularForm Manifold MatrixGroups

namespace ThreeOmittedValues

noncomputable def orbitHeightLower (τ : UpperHalfPlane) : ℝ :=
  (τ : ℂ).im / (4 * ((|(τ : ℂ).re| + 1) ^ 2 + (τ : ℂ).im ^ 2))

noncomputable def orbitHeightUpper (τ : UpperHalfPlane) : ℝ :=
  1 / (4 * (τ : ℂ).im)

noncomputable def gaussianBetaConstant : ℝ :=
  (gaussianScale / 2) * Real.exp (gaussianScale ^ 2)

noncomputable def orbitLogConstant (τ : UpperHalfPlane) : ℝ :=
  17 + 2 * (3 * orbitStripBound τ + 2) ^ 2

theorem orbitHeightLower_pos (τ : UpperHalfPlane) : 0 < orbitHeightLower τ := by
  have h : 0 < (τ : ℂ).im := τ.im_pos
  unfold orbitHeightLower
  positivity

theorem orbitHeightUpper_pos (τ : UpperHalfPlane) : 0 < orbitHeightUpper τ := by
  have h : 0 < (τ : ℂ).im := τ.im_pos
  unfold orbitHeightUpper
  positivity

theorem gaussianBetaConstant_pos : 0 < gaussianBetaConstant := by
  unfold gaussianBetaConstant
  exact mul_pos (half_pos gaussianScale_pos) (Real.exp_pos _)

theorem orbitLogConstant_pos (τ : UpperHalfPlane) : 0 < orbitLogConstant τ := by
  unfold orbitLogConstant
  positivity

theorem shiftedOrbit_height_bounds (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane)
    (i : OrbitIndexFrom N) :
    orbitHeightLower τ / (i.1.1 : ℝ) ^ 2 ≤
        (shiftedOrbitPoint N hN (logarithmicOrbitShift τ) τ i).im ∧
      (shiftedOrbitPoint N hN (logarithmicOrbitShift τ) τ i).im ≤
        orbitHeightUpper τ / (i.1.1 : ℝ) ^ 2 := by
  rw [shiftedOrbitPoint_im]
  simpa [orbitHeightLower, orbitHeightUpper, div_mul_eq_div_div] using
    orbitPoint_height_bounds N hN τ i

theorem shiftedOrbit_gaussian_beta_bound (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane)
    (i : OrbitIndexFrom N) (hlog : 1 ≤ Real.log (i.1.1 : ℝ)) :
    gaussianBeta (shiftedOrbitPoint N hN (logarithmicOrbitShift τ) τ i).re ≤
      gaussianBetaConstant / (i.1.1 : ℝ) ^ 4 := by
  let m : ℝ := i.1.1
  let x : ℝ := (shiftedOrbitPoint N hN (logarithmicOrbitShift τ) τ i).re
  have hm : 0 < m := by
    dsimp [m]
    have := i.1.2
    exact_mod_cast (show 0 < i.1.1 by omega)
  have hx := logarithmicOrbitShift_bounds N hN τ i hlog
  have hx2 : 8 * Real.log m ≤ x ^ 2 := hx.2.1
  have hexp : Real.exp (-(x ^ 2) / 2) ≤ Real.exp (-(4 * Real.log m)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hpow : Real.exp (-(4 * Real.log m)) = ((m ^ 4)⁻¹) := by
    rw [Real.exp_neg]
    have h4 : Real.exp (4 * Real.log m) = m ^ 4 := by
      simpa only [Nat.cast_ofNat, Real.exp_log hm] using (Real.exp_nat_mul (Real.log m) 4)
    rw [h4]
  have hβ := gaussianBeta_upper x
  unfold gaussianBetaConstant
  rw [div_eq_mul_inv]
  rw [hpow] at hexp
  exact hβ.trans (mul_le_mul_of_nonneg_left hexp
    (mul_nonneg (half_pos gaussianScale_pos).le (Real.exp_pos _).le))

theorem shiftedOrbit_log_denominator (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane)
    (i : OrbitIndexFrom N) (hlog : 1 ≤ Real.log (i.1.1 : ℝ)) :
    1 + (shiftedOrbitPoint N hN (logarithmicOrbitShift τ) τ i).re ^ 2 ≤
      orbitLogConstant τ * Real.log (i.1.1 : ℝ) := by
  have hx := (logarithmicOrbitShift_bounds N hN τ i hlog).2.2
  unfold orbitLogConstant
  nlinarith

end ThreeOmittedValues
