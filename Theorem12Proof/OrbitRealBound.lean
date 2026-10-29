module

public import Theorem12Proof.SelectedOrbitPoints
import Mathlib.Tactic

/-!
# A uniform horizontal bound for unshifted orbit points

The bounded choice of the upper-left matrix entry places every selected
point in a fixed vertical strip depending only on the original point `τ`.
-/

@[expose] public section

open Complex UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

namespace ThreeOmittedValues

theorem orbitPoint_norm_le (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane)
    (i : OrbitIndexFrom N) :
    ‖orbitPoint N hN τ i‖ ≤ 2 + 1 / (τ : ℂ).im := by
  let a : ℝ := orbitA N hN i
  let b : ℝ := orbitB N hN i
  let c : ℝ := 2 * (i.1.1 : ℝ)
  let d : ℝ := i.2.1
  have hm : (2 : ℝ) ≤ (i.1.1 : ℝ) := by
    have := i.1.2
    exact_mod_cast (show 2 ≤ i.1.1 by omega)
  have hc : (1 : ℝ) ≤ c := by dsimp [c]; linarith
  have hcp : 0 < c := by linarith
  have hτpos : 0 < (τ : ℂ).im := τ.im_pos
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have halt : a ≤ 2 * c := by
    have h := (orbit_entries_spec N hN i).2.1
    have h' : (orbitA N hN i : ℝ) < 4 * (i.1.1 : ℝ) := by exact_mod_cast h
    dsimp [a, c]
    linarith
  have hdet : a * d - c * b = 1 := by
    have h : (orbitA N hN i : ℝ) * (i.2.1 : ℝ) =
        2 * (i.1.1 : ℝ) * (orbitB N hN i : ℝ) + 1 := by
      exact_mod_cast (orbit_entries_spec N hN i).2.2.1
    dsimp [a, b, c, d]
    linarith
  let den : ℂ := (c : ℂ) * (τ : ℂ) + (d : ℂ)
  have hdenim : den.im = c * (τ : ℂ).im := by simp [den]
  have hdenpos : 0 < den.im := by rw [hdenim]; exact mul_pos hcp hτpos
  have hden : den ≠ 0 := by
    intro h
    rw [h] at hdenpos
    simp at hdenpos
  have hdennorm : c * (τ : ℂ).im ≤ ‖den‖ := by
    have h := Complex.abs_im_le_norm den
    rw [hdenim] at h
    simpa only [abs_of_pos (mul_pos hcp hτpos)] using h
  have hnormlower : (τ : ℂ).im ≤ ‖(c : ℂ) * den‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcp]
    have h₁ := mul_le_mul_of_nonneg_left hdennorm hcp.le
    have h₂ : (τ : ℂ).im ≤ c * (c * (τ : ℂ).im) := by
      have hc2 : 1 ≤ c * c := by nlinarith
      have h := mul_le_mul_of_nonneg_right hc2 hτpos.le
      nlinarith
    linarith
  have hdennormpos : 0 < ‖(c : ℂ) * den‖ := lt_of_lt_of_le hτpos hnormlower
  have hquot : ‖(a : ℂ) / (c : ℂ)‖ ≤ 2 := by
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_pos hcp]
    exact (div_le_iff₀ hcp).2 halt
  have hfrac : ‖1 / ((c : ℂ) * den)‖ ≤ 1 / (τ : ℂ).im := by
    simp only [norm_div, norm_one]
    exact one_div_le_one_div_of_le hτpos hnormlower
  have hrep : orbitPoint N hN τ i =
      ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / den := by
    change (((orbitMatrix N hN i • τ : UpperHalfPlane) : ℂ)) = _
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [orbitMatrix, a, b, c, d, den]
  have hdetC : (a : ℂ) * d - (c : ℂ) * b = 1 := by exact_mod_cast hdet
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcp.ne'
  have hid := mobius_orbit_identity (z := (τ : ℂ)) hcC hden hdetC
  rw [hrep, hid]
  exact (norm_sub_le _ _).trans (add_le_add hquot hfrac)

theorem orbitPoint_real_abs_le (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane)
    (i : OrbitIndexFrom N) :
    |(orbitPoint N hN τ i).re| ≤ 2 + 1 / (τ : ℂ).im :=
  (Complex.abs_re_le_norm _).trans (orbitPoint_norm_le N hN τ i)

end ThreeOmittedValues
