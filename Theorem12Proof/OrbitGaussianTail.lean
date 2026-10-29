module

public import Theorem12Proof.LogarithmicOrbitGeometry
public import Theorem12Proof.OrbitEventualThreshold
import Mathlib.Tactic

/-!
# The shifted orbit eventually lies above twice the Gaussian boundary

The proof uses a concrete elementary threshold, rather than an unproved
asymptotic assumption.
-/

@[expose] public section

open Complex UpperHalfPlane CongruenceSubgroup Set
open scoped ModularForm Manifold MatrixGroups

namespace ThreeOmittedValues

theorem exists_shifted_orbit_gaussian_tail (τ : UpperHalfPlane) :
    ∃ (N : ℕ) (hN : 2 ≤ N), ∀ i : OrbitIndexFrom N,
      let w := shiftedOrbitPoint N hN (logarithmicOrbitShift τ) τ i
      w.im ≤ 1 ∧ gaussianBeta w.re ≤ w.im / 2 ∧
      1 + w.re ^ 2 ≤ orbitLogConstant τ * Real.log (i.1.1 : ℝ) ∧
      orbitHeightLower τ / (i.1.1 : ℝ) ^ 2 ≤ w.im := by
  obtain ⟨N, hN, hthreshold⟩ := exists_orbit_threshold
    (orbitHeightLower_pos τ) (orbitHeightUpper_pos τ) gaussianBetaConstant_pos
  refine ⟨N, hN, ?_⟩
  intro i
  obtain ⟨hlog, hupper, hsmall⟩ := hthreshold i.1.1 i.1.2
  let m : ℝ := i.1.1
  let w : ℂ := shiftedOrbitPoint N hN (logarithmicOrbitShift τ) τ i
  have hm : 0 < m := by
    dsimp [m]
    have := i.1.2
    exact_mod_cast (show 0 < i.1.1 by omega)
  have hm2 : 0 < m ^ 2 := by positivity
  have hm4 : 0 < m ^ 4 := by positivity
  have hheight := shiftedOrbit_height_bounds N hN τ i
  have hbeta := shiftedOrbit_gaussian_beta_bound N hN τ i hlog
  have hden := shiftedOrbit_log_denominator N hN τ i hlog
  have hw1 : w.im ≤ 1 := by
    have h : orbitHeightUpper τ / m ^ 2 ≤ 1 :=
      (div_le_iff₀ hm2).2 (by simpa [m] using hupper)
    dsimp [w, m] at *
    linarith
  have hfrac : gaussianBetaConstant / m ^ 4 ≤ orbitHeightLower τ / (2 * m ^ 2) := by
    apply (div_le_div_iff₀ hm4 (by positivity : 0 < 2 * m ^ 2)).2
    have hmul := mul_le_mul_of_nonneg_right hsmall (sq_nonneg m)
    dsimp [m] at *
    nlinarith
  have hhalf : orbitHeightLower τ / (2 * m ^ 2) =
      (orbitHeightLower τ / m ^ 2) / 2 := by
    field_simp
  have hwβ : gaussianBeta w.re ≤ w.im / 2 := by
    rw [hhalf] at hfrac
    dsimp [w, m] at *
    linarith
  exact ⟨hw1, hwβ, hden, hheight.1⟩

end ThreeOmittedValues
