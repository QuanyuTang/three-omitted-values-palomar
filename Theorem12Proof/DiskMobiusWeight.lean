module

public import Theorem12Proof.Vendor.DirichletRiemannMapping
import Mathlib.Tactic

/-!
# Disk automorphisms preserve the Blaschke condition

This provides the quantitative comparison needed when the normalization
point for Jensen's formula is moved by a disk automorphism.
-/

@[expose] public section

open Complex Metric Set

namespace ThreeOmittedValues

theorem mob_blaschke_weight_comparison {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    (1 - ‖a‖ ^ 2) * (1 - ‖z‖) ≤ 8 * (1 - ‖mob a z‖) := by
  let D : ℂ := 1 - (starRingEnd ℂ) a * z
  have hD : D ≠ 0 := mob_denom_ne_zero ha hz
  have hDn : ‖D‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  have hidentity : ‖D‖ ^ 2 - ‖z - a‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    simpa only [D, normSq_eq_norm_sq] using normSq_identity a z
  have hformula : ‖mob a z‖ = ‖z - a‖ / ‖D‖ := by
    simp only [mob, norm_div, D]
  have hmul : ‖mob a z‖ ^ 2 * ‖D‖ ^ 2 = ‖z - a‖ ^ 2 := by
    rw [hformula]
    field_simp
  have heq : (1 - ‖mob a z‖ ^ 2) * ‖D‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    nlinarith [hidentity, hmul]
  have hprod : ‖a‖ * ‖z‖ ≤ 1 := by
    calc
      ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hz.le (norm_nonneg a)
      _ ≤ 1 := by simpa using ha.le
  have hDbound : ‖D‖ ≤ 2 := by
    calc
      ‖D‖ ≤ ‖(1 : ℂ)‖ + ‖(starRingEnd ℂ) a * z‖ := norm_sub_le _ _
      _ = 1 + ‖a‖ * ‖z‖ := by simp [norm_mul]
      _ ≤ 2 := by linarith
  have hDsq : ‖D‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg D]
  have hm : ‖mob a z‖ < 1 := norm_mob_lt_one ha hz
  have hc : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hm2 : 0 ≤ 1 - ‖mob a z‖ ^ 2 := by nlinarith [norm_nonneg (mob a z)]
  have hzcmp : 1 - ‖z‖ ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hmcmp : 1 - ‖mob a z‖ ^ 2 ≤ 2 * (1 - ‖mob a z‖) := by
    nlinarith [sq_nonneg (1 - ‖mob a z‖)]
  calc
    (1 - ‖a‖ ^ 2) * (1 - ‖z‖) ≤ (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hzcmp hc
    _ = (1 - ‖mob a z‖ ^ 2) * ‖D‖ ^ 2 := heq.symm
    _ ≤ (1 - ‖mob a z‖ ^ 2) * 4 := mul_le_mul_of_nonneg_left hDsq hm2
    _ ≤ 8 * (1 - ‖mob a z‖) := by linarith

end ThreeOmittedValues
