module

public import Theorem12Proof.ClosedHalfPlaneExtension
public import Theorem12Proof.CompactGraphFrontier
import Mathlib.Tactic

/-!
# Boundary values of the normalized Farey map

Every finite real boundary point is sent to a finite point on the Farey
graph. This turns the closed-disk homeomorphism into the boundary data
needed for Schwarz reflection.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem halfPlaneToCayley_norm_of_im_zero {z : ℂ} (hz : z.im = 0) :
    ‖halfPlaneToCayley z‖ = 1 := by
  have hden : z + Complex.I ≠ 0 := add_I_ne_zero_of_im_nonneg (by linarith)
  have hs : ‖z - Complex.I‖ ^ 2 = ‖z + Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, hz]
  have heq : ‖z - Complex.I‖ = ‖z + Complex.I‖ := by
    nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
  unfold halfPlaneToCayley
  rw [norm_div, heq, div_self (norm_ne_zero_iff.mpr hden)]

theorem halfPlaneContinuousExtension_boundary {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) {z : ℂ} (hz : z.im = 0) :
    ∃ x : ℝ, halfPlaneContinuousExtension e z = graphMap (pastedFareyHeight levels) x := by
  let h := pastedFareyHeight levels
  let D := halfPlaneToCayley '' upperGraphDomain h
  have h0 : ∀ x, 0 ≤ h x := pastedFareyHeight_nonneg levels
  have hh : Continuous h := pastedFareyHeight_continuous levels
  have hDopen : IsOpen D := by
    apply cayleyPartialHomeomorph.isOpen_image_of_subset_source (upperGraphDomain_isOpen hh)
    intro v hv
    change v + Complex.I ≠ 0
    exact add_I_ne_zero_of_im_pos ((h0 v.re).trans_lt hv)
  have hz0 : 0 ≤ z.im := by linarith
  let q : closedBall (0 : ℂ) 1 := closedHalfPlaneCayley ⟨z, hz0⟩
  have hqnorm : ‖(q : ℂ)‖ = 1 := halfPlaneToCayley_norm_of_im_zero hz
  have hqnot : (q : ℂ) ∉ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hqnorm]
    exact lt_irrefl 1
  have heqnot : (e q : ℂ) ∉ D := by
    intro hmem
    obtain ⟨w, hw, hwq⟩ := hmem
    rw [← hΦimage] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    let qu : closedBall (0 : ℂ) 1 := closedHalfPlaneCayley ⟨u, hu.le⟩
    have hqu : (qu : ℂ) ∈ ball (0 : ℂ) 1 := halfPlaneToCayley_mem_ball hu
    have hequ : (e qu : ℂ) = halfPlaneToCayley (Φ u) := by
      simpa only [qu, closedHalfPlaneCayley, cayleyToHalfPlane_halfPlaneToCayley hu] using he qu hqu
    have hequal : e q = e qu := Subtype.ext (hwq.symm.trans hequ.symm)
    have hqeq := congrArg Subtype.val (e.injective hequal)
    rw [hqeq] at hqnot
    exact hqnot hqu
  have hfront : (e q : ℂ) ∈ frontier D := by
    rw [hDopen.frontier_eq]
    exact ⟨(e q).2, heqnot⟩
  have hne : (e q : ℂ) ≠ 1 := closedDiskBoundaryImage_ne_one e he1 ⟨z, hz0⟩
  rw [frontier_compactGraphDomain hh h0] at hfront
  simp only [mem_insert_iff, mem_range, Function.comp_apply] at hfront
  rcases hfront with hbad | ⟨x, hx⟩
  · exact False.elim (hne hbad)
  · refine ⟨x, ?_⟩
    rw [halfPlaneContinuousExtension, dif_pos hz0]
    change cayleyToHalfPlane (e q) = graphMap h x
    rw [← hx]
    exact cayleyToHalfPlane_halfPlaneToCayley_of_denominator (graph_denominator_ne h0 x)

end ThreeOmittedValues
