module

public import Theorem12Proof.JensenLimit
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Blaschke summability for injective families of zeros

This is the disk zero-set theorem needed for the bounded-type argument,
currently for functions whose value at the origin is nonzero. The case of
a zero at the origin and the half-plane change of variables remain separate.
-/

@[expose] public section

open Set Metric

namespace ThreeOmittedValues

/-- Any injective family of zeros of a bounded analytic function normalized
at the origin has summable disk Blaschke weights. -/
theorem summable_zero_weights_of_normalized {ι : Type*} (a : ι → ℂ)
    (ha : Function.Injective a) {f : ℂ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hf0 : f 0 = 1)
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ Real.exp L)
    (hzeros : ∀ i, a i ∈ ball (0 : ℂ) 1 ∧ f (a i) = 0) :
    Summable (fun i => 1 - ‖a i‖) := by
  classical
  apply summable_of_sum_le (c := L)
  · intro i
    change 0 ≤ 1 - ‖a i‖
    have hi : ‖a i‖ < 1 := by
      simpa only [mem_ball, dist_zero_right] using (hzeros i).1
    linarith
  · intro s
    have hpoints : ∀ z ∈ s.image a, z ∈ ball (0 : ℂ) 1 ∧ f z = 0 := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact hzeros i
    have h := finite_zero_blaschke_sum_le (s.image a) hL hf hf0 hbound hpoints
    rw [Finset.sum_image ha.injOn] at h
    exact h

/-- Normalization by the nonzero value at the origin removes the
requirement that this value equal one. -/
theorem summable_zero_weights_of_nonzero_origin {ι : Type*} (a : ι → ℂ)
    (ha : Function.Injective a) {f : ℂ → ℂ} {C : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hf0 : f 0 ≠ 0)
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ C)
    (hzeros : ∀ i, a i ∈ ball (0 : ℂ) 1 ∧ f (a i) = 0) :
    Summable (fun i => 1 - ‖a i‖) := by
  have hnorm : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hC : ‖f 0‖ ≤ C := hbound 0 (by simp)
  have hCpos : 0 < C := hnorm.trans_le hC
  let L := Real.log (C / ‖f 0‖)
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_div hnorm).2 hC)
  have hexp : Real.exp L = C / ‖f 0‖ := Real.exp_log (div_pos hCpos hnorm)
  have hnormBound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z / f 0‖ ≤ Real.exp L := by
    intro z hz
    rw [hexp, norm_div]
    exact div_le_div_of_nonneg_right (hbound z hz) hnorm.le
  have hnormalized : (fun z => f z / f 0) 0 = 1 := div_self hf0
  apply summable_zero_weights_of_normalized a ha hL hf.div_const hnormalized hnormBound
  intro i
  exact ⟨(hzeros i).1, by rw [(hzeros i).2]; simp⟩

end ThreeOmittedValues
