module

public import Theorem12Proof.ShiftedOrbitPoints
public import Theorem12Proof.OrbitRealBound
import Mathlib.Tactic

/-!
# Choosing the logarithmic orbit shift

The shift places all level-`m` points at horizontal distance of order
`√(log m)` while retaining their modular fibre and height estimates.
-/

@[expose] public section

open Complex UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

namespace ThreeOmittedValues

noncomputable def orbitStripBound (τ : UpperHalfPlane) : ℝ := 2 + 1 / (τ : ℂ).im

theorem orbitStripBound_pos (τ : UpperHalfPlane) : 0 < orbitStripBound τ := by
  have hτ : 0 < (τ : ℂ).im := τ.im_pos
  unfold orbitStripBound
  positivity

noncomputable def logarithmicOrbitShift (τ : UpperHalfPlane) (m : ℕ) : ℤ :=
  ⌈Real.sqrt (2 * Real.log (m : ℝ)) + orbitStripBound τ⌉

theorem logarithmicOrbitShift_bounds (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane)
    (i : OrbitIndexFrom N) (hlog : 1 ≤ Real.log (i.1.1 : ℝ)) :
    let x := (shiftedOrbitPoint N hN (logarithmicOrbitShift τ) τ i).re
    0 ≤ x ∧ 8 * Real.log (i.1.1 : ℝ) ≤ x ^ 2 ∧
      x ^ 2 ≤ (16 + 2 * (3 * orbitStripBound τ + 2) ^ 2) *
        Real.log (i.1.1 : ℝ) := by
  let B := orbitStripBound τ
  let L := Real.log (i.1.1 : ℝ)
  let q := Real.sqrt (2 * L)
  let r := (orbitPoint N hN τ i).re
  let x := (shiftedOrbitPoint N hN (logarithmicOrbitShift τ) τ i).re
  have hB : 0 < B := orbitStripBound_pos τ
  have hL : 1 ≤ L := hlog
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 2 * L := by
    dsimp [q]
    rw [Real.sq_sqrt (by linarith : 0 ≤ 2 * L)]
  have hr : |r| ≤ B := orbitPoint_real_abs_le N hN τ i
  have hceil : q + B ≤ (logarithmicOrbitShift τ i.1.1 : ℝ) := by
    exact Int.le_ceil _
  have hceilupper : (logarithmicOrbitShift τ i.1.1 : ℝ) < q + B + 1 := by
    exact Int.ceil_lt_add_one _
  have hx : x = r + 2 * (logarithmicOrbitShift τ i.1.1 : ℝ) := by
    dsimp [x, r]
    rw [shiftedOrbitPoint_eq]
    simp
  have hxlo : 2 * q ≤ x := by
    have hrlo := (abs_le.mp hr).1
    linarith
  have hxhi : x ≤ 2 * q + (3 * B + 2) := by
    have hrhi := (abs_le.mp hr).2
    linarith
  have hx0 : 0 ≤ x := by linarith
  have hlowprod := mul_nonneg (sub_nonneg.mpr hxlo) (by linarith : 0 ≤ x + 2 * q)
  have hhighprod := mul_nonneg (sub_nonneg.mpr hxhi) (by linarith : 0 ≤ x + (2 * q + (3 * B + 2)))
  have hsq : x ^ 2 ≤ 16 * L + 2 * (3 * B + 2) ^ 2 := by
    nlinarith [sq_nonneg (2 * q - (3 * B + 2))]
  have hmul : 2 * (3 * B + 2) ^ 2 ≤ 2 * (3 * B + 2) ^ 2 * L := by
    nlinarith [sq_nonneg (3 * B + 2)]
  exact ⟨hx0, by nlinarith, by nlinarith⟩

end ThreeOmittedValues
