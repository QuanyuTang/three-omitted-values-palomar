module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Tactic

/-!
# A finite Blaschke estimate from Jensen's formula

This file develops a zero-set estimate needed to rule out bounded type. It
does not assert the existence of the meromorphic function in the paper.
-/

@[expose] public section

open Set Metric Real

namespace ThreeOmittedValues

/-- A bounded analytic function normalized to one at the origin controls
the finite sum of radial distances of its zeros from an inner circle. -/
theorem finite_zero_radial_sum_le (s : Finset ℂ) {f : ℂ → ℂ}
    {r R L : ℝ} (hr : 0 < r) (hrR : r < R) (hR1 : R ≤ 1) (hL : 0 ≤ L)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 = 1)
    (hbound : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ Real.exp L)
    (hzeros : ∀ z ∈ s, z ∈ closedBall 0 r ∧ f z = 0) :
    ∑ z ∈ s, (R - ‖z‖) ≤ L := by
  classical
  have hR : 0 < R := hr.trans hrR
  have h0 : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have hf0ne : f 0 ≠ 0 := by simp [hf0]
  have hord0 : meromorphicOrderAt f 0 = 0 :=
    (hf 0 h0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf0ne
  have hfinite : ∀ z ∈ closedBall 0 R, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz
    apply hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected h0 hz
    simp [hord0]
  let D := MeromorphicOn.divisor f (closedBall 0 R)
  have hDnonneg : 0 ≤ D := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  have hfin := D.finiteSupport (isCompact_closedBall (0 : ℂ) R)
  let T : Finset ℂ := hfin.toFinset
  have hzeroD : ∀ z ∈ s, 1 ≤ D z := by
    intro z hz
    have hzR : z ∈ closedBall (0 : ℂ) R :=
      closedBall_subset_closedBall hrR.le (hzeros z hz).1
    have hne : meromorphicOrderAt f z ≠ 0 := by
      intro hzero
      exact ((hf z hzR).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hzero)
        (hzeros z hz).2
    have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f z :=
      lt_of_le_of_ne (hf z hzR).meromorphicOrderAt_nonneg (Ne.symm hne)
    have hcoe : ((D z : ℤ) : WithTop ℤ) = meromorphicOrderAt f z := by
      dsimp [D]
      rw [MeromorphicOn.divisor_apply hf.meromorphicOn hzR]
      exact WithTop.coe_untop₀_of_ne_top (hfinite z hzR)
    have hdpos : (0 : ℤ) < D z := by
      exact_mod_cast (show (0 : WithTop ℤ) < (D z : WithTop ℤ) by rw [hcoe]; exact hpos)
    linarith
  have hST : s ⊆ T := by
    intro z hz
    simp only [T, Set.Finite.mem_toFinset, Function.mem_support]
    have := hzeroD z hz
    linarith
  have hsum :
      (∑ᶠ u, (D u : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹)) =
        ∑ u ∈ T, (D u : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support, ne_eq] at hu
    simp only [T, Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
    intro hzero
    exact hu (by simp [hzero])
  have hf' : AnalyticOnNhd ℂ f (closedBall 0 |R|) := by
    simpa only [abs_of_pos hR] using hf
  have hJ := hf'.circleAverage_log_norm hR.ne' hf0ne
  rw [abs_of_pos hR] at hJ
  change circleAverage (fun z => Real.log ‖f z‖) 0 R =
    (∑ᶠ u, (D u : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹)) + Real.log ‖f 0‖ at hJ
  rw [hsum, hf0] at hJ
  simp only [norm_one, Real.log_one, add_zero] at hJ
  have havg : circleAverage (fun z => Real.log ‖f z‖) 0 R ≤ L := by
    apply circleAverage_mono_on_of_le_circle
      (circleIntegrable_log_norm_meromorphicOn (show MeromorphicOn f (sphere 0 |R|) by
        intro z hz
        exact hf.meromorphicOn z (sphere_subset_closedBall
          (by simpa only [abs_of_pos hR] using hz))))
    intro z hz
    have hzR : z ∈ sphere (0 : ℂ) R := by simpa only [abs_of_pos hR] using hz
    by_cases hz0 : f z = 0
    · simpa only [hz0, norm_zero, Real.log_zero] using hL
    · simpa only [Real.log_exp] using
        Real.log_le_log (norm_pos_iff.mpr hz0) (hbound z hzR)
  have hterm : ∀ u ∈ T, 0 ≤ (D u : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹) := by
    intro u hu
    apply mul_nonneg (by exact_mod_cast hDnonneg u)
    by_cases huc : u = 0
    · simp [huc]
    · have huR : u ∈ closedBall (0 : ℂ) R := D.supportWithinDomain (by simpa [T] using hu)
      have hnorm : 0 < ‖(0 : ℂ) - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
      have hdist : ‖(0 : ℂ) - u‖ ≤ R := by
        simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using huR
      rw [← div_eq_mul_inv]
      exact Real.log_nonneg ((le_div_iff₀ hnorm).mpr (by simpa using hdist))
  have hsingle : ∀ z ∈ s,
      R - ‖z‖ ≤ (D z : ℝ) * Real.log (R * ‖(0 : ℂ) - z‖⁻¹) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro heq
      have hzval := (hzeros z hz).2
      rw [heq, hf0] at hzval
      exact one_ne_zero hzval
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hdist : ‖z‖ ≤ r := by
      simpa only [mem_closedBall, dist_zero_right] using (hzeros z hz).1
    have hnonneg : 0 ≤ R - ‖z‖ := by linarith
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hR hnorm)
    have hcompare : R - ‖z‖ ≤ Real.log (R * ‖(0 : ℂ) - z‖⁻¹) := by
      simp only [zero_sub, norm_neg, ← div_eq_mul_inv, inv_div] at hlog ⊢
      have hfrac : R - ‖z‖ ≤ (R - ‖z‖) / R := by
        apply (le_div_iff₀ hR).2
        nlinarith [mul_nonneg (sub_nonneg.mpr hR1) hnonneg]
      have heq : (R - ‖z‖) / R = 1 - ‖z‖ / R := by field_simp
      linarith
    have hlognonneg : 0 ≤ Real.log (R * ‖(0 : ℂ) - z‖⁻¹) :=
      hnonneg.trans hcompare
    calc
      R - ‖z‖ ≤ Real.log (R * ‖(0 : ℂ) - z‖⁻¹) := hcompare
      _ = 1 * Real.log (R * ‖(0 : ℂ) - z‖⁻¹) := (one_mul _).symm
      _ ≤ (D z : ℝ) * Real.log (R * ‖(0 : ℂ) - z‖⁻¹) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hzeroD z hz) hlognonneg
  calc
    ∑ z ∈ s, (R - ‖z‖) ≤ ∑ z ∈ s, (D z : ℝ) * Real.log (R * ‖(0 : ℂ) - z‖⁻¹) :=
      Finset.sum_le_sum hsingle
    _ ≤ ∑ z ∈ T, (D z : ℝ) * Real.log (R * ‖(0 : ℂ) - z‖⁻¹) :=
      Finset.sum_le_sum_of_subset_of_nonneg hST (fun z hz _ => hterm z hz)
    _ = circleAverage (fun z => Real.log ‖f z‖) 0 R := hJ.symm
    _ ≤ L := havg

end ThreeOmittedValues
