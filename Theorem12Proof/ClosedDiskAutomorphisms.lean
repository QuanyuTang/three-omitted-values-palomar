module

public import Theorem12Proof.Vendor.DirichletRiemannMapping
import Mathlib.Tactic

/-!
# Disk automorphisms on the closed disk

The usual Möbius automorphisms and rotations extend to explicit
homeomorphisms of the closed unit disk. These will permit simultaneous
normalization at an interior point and a boundary point.
-/

@[expose] public section

open Complex Metric Set

namespace ThreeOmittedValues

theorem mob_denom_ne_zero_closed {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * z = 1 := by linear_combination -h
  have hnorm : ‖(starRingEnd ℂ) a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc
      ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
      _ < 1 := by linarith
  rw [h1] at hnorm
  simp at hnorm

theorem norm_mob_le_one_closed {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖mob a z‖ ≤ 1 := by
  have hd := mob_denom_ne_zero_closed ha hz
  unfold mob
  rw [norm_div, div_le_one (norm_pos_iff.mpr hd)]
  have hid := normSq_identity a z
  have ha2 : 0 ≤ 1 - normSq a := by
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hz2 : 0 ≤ 1 - normSq z := by
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hs : normSq (z - a) ≤ normSq (1 - (starRingEnd ℂ) a * z) := by
    nlinarith [mul_nonneg ha2 hz2]
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]

theorem mob_neg_mob_closed {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    mob (-a) (mob a z) = z := by
  have hd := mob_denom_ne_zero_closed ha hz
  have hna : 1 - (starRingEnd ℂ) a * a ≠ 0 := mob_denom_ne_zero_closed ha ha.le
  unfold mob
  rw [map_neg]
  have h2 : 1 - -(starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) =
      (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) := by
    field_simp
    ring
  rw [h2, div_eq_iff (div_ne_zero hna hd)]
  generalize (starRingEnd ℂ) a = c at *
  rw [div_sub' hd, mul_div_assoc', div_left_inj' hd]
  ring

/-- The automorphism `mob (-a)` sends the disk center to `a`. -/
noncomputable def mobClosedDiskHomeomorph (a : ℂ) (ha : ‖a‖ < 1) :
    closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 where
  toFun z := ⟨mob (-a) z, mem_closedBall_zero_iff.mpr
    (norm_mob_le_one_closed (by simpa using ha) (mem_closedBall_zero_iff.mp z.2))⟩
  invFun z := ⟨mob a z, mem_closedBall_zero_iff.mpr
    (norm_mob_le_one_closed ha (mem_closedBall_zero_iff.mp z.2))⟩
  left_inv z := by
    apply Subtype.ext
    have h := mob_neg_mob_closed (a := -a) (by simpa using ha) (mem_closedBall_zero_iff.mp z.2)
    simpa only [neg_neg] using h
  right_inv z := by
    apply Subtype.ext
    exact mob_neg_mob_closed ha (mem_closedBall_zero_iff.mp z.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro z
    have hden := mob_denom_ne_zero_closed (a := -a) (by simpa using ha)
      (mem_closedBall_zero_iff.mp z.2)
    have hc : ContinuousAt (mob (-a)) (z : ℂ) := by
      unfold mob
      fun_prop (disch := exact hden)
    exact hc.comp continuous_subtype_val.continuousAt
  continuous_invFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro z
    have hden := mob_denom_ne_zero_closed ha (mem_closedBall_zero_iff.mp z.2)
    have hc : ContinuousAt (mob a) (z : ℂ) := by
      unfold mob
      fun_prop (disch := exact hden)
    exact hc.comp continuous_subtype_val.continuousAt

/-- A rotation by a unit complex number is a closed-disk homeomorphism. -/
noncomputable def rotationClosedDiskHomeomorph (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 where
  toFun z := ⟨ζ * z, mem_closedBall_zero_iff.mpr (by
    simpa [norm_mul, hζ] using mem_closedBall_zero_iff.mp z.2)⟩
  invFun z := ⟨ζ⁻¹ * z, mem_closedBall_zero_iff.mpr (by
    simpa [norm_mul, norm_inv, hζ] using mem_closedBall_zero_iff.mp z.2)⟩
  left_inv z := by
    apply Subtype.ext
    have hne : ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hζ]; norm_num)
    simp [← mul_assoc, hne]
  right_inv z := by
    apply Subtype.ext
    have hne : ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hζ]; norm_num)
    simp [← mul_assoc, hne]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val

end ThreeOmittedValues
