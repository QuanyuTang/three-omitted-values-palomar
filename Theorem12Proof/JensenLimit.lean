module

public import Theorem12Proof.JensenBlaschke
import Mathlib.Tactic

/-!
# The Blaschke estimate for finite sets of zeros

The radius in Jensen's inequality tends to one while the finite zero set
is held fixed. This proves the uniform finite-set bound for a bounded
analytic function normalized at the origin.
-/

@[expose] public section

open Set Metric Filter
open scoped Topology

namespace ThreeOmittedValues

theorem finite_zero_blaschke_sum_le (s : Finset ℂ) {f : ℂ → ℂ} {L : ℝ}
    (hL : 0 ≤ L) (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hf0 : f 0 = 1)
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ Real.exp L)
    (hzeros : ∀ z ∈ s, z ∈ ball (0 : ℂ) 1 ∧ f z = 0) :
    ∑ z ∈ s, (1 - ‖z‖) ≤ L := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨z₀, hz₀, hmax⟩ := Finset.exists_max_image s (fun z => ‖z‖) hs
    have hzlt : ‖z₀‖ < 1 := by
      simpa only [mem_ball, dist_zero_right] using (hzeros z₀ hz₀).1
    let r := (‖z₀‖ + 1) / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hr1 : r < 1 := by dsimp [r]; linarith
    have hrs : ∀ z ∈ s, z ∈ closedBall (0 : ℂ) r ∧ f z = 0 := by
      intro z hz
      have hle : ‖z‖ ≤ r := by
        have hm := hmax z hz
        dsimp [r]
        linarith
      exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hle, (hzeros z hz).2⟩
    let R : ℕ → ℝ := fun n => 1 - (1 - r) / ((n : ℝ) + 2)
    have hR (n : ℕ) : r < R n ∧ R n < 1 := by
      have hden : (1 : ℝ) < (n : ℝ) + 2 := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        linarith
      have hnum : 0 < 1 - r := by linarith
      have hdivpos : 0 < (1 - r) / ((n : ℝ) + 2) := by positivity
      have hdivlt : (1 - r) / ((n : ℝ) + 2) < 1 - r := div_lt_self hnum hden
      dsimp [R]
      constructor <;> linarith
    have hboundR (n : ℕ) : ∀ z ∈ sphere (0 : ℂ) (R n), ‖f z‖ ≤ Real.exp L := by
      intro z hz
      apply hbound z
      exact closedBall_subset_ball (hR n).2 (sphere_subset_closedBall hz)
    have hall (n : ℕ) : ∑ z ∈ s, (R n - ‖z‖) ≤ L := by
      apply finite_zero_radial_sum_le s hr (hR n).1 (hR n).2.le hL
        (hf.mono (closedBall_subset_ball (hR n).2)) hf0 (hboundR n) hrs
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hlim : Tendsto R atTop (𝓝 1) := by
      simpa only [R, sub_zero] using
        (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hden) :
          Tendsto (fun n : ℕ => 1 - (1 - r) / ((n : ℝ) + 2)) atTop (𝓝 (1 - 0)))
    have hlimsum : Tendsto (fun n : ℕ => ∑ z ∈ s, (R n - ‖z‖)) atTop
        (𝓝 (∑ z ∈ s, (1 - ‖z‖))) := by
      exact tendsto_finsetSum _ fun z _ => hlim.sub tendsto_const_nhds
    exact le_of_tendsto hlimsum (Filter.Eventually.of_forall hall)
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simpa [he] using hL

end ThreeOmittedValues
