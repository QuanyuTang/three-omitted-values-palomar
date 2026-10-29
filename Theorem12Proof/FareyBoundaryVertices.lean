module

public import Theorem12Proof.NormalizedFareyMap
import Mathlib.Tactic

/-!
# Real boundary parameters for the Farey graph

Every finite graph point has a unique real preimage under the normalized
closed-disk boundary correspondence. The modular cusp value at that point
is a separate analytic question.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem unique_real_boundary_parameter {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ) :
    ∃! ξ : ℝ, ∃ q : closedBall (0 : ℂ) 1,
      ‖(q : ℂ)‖ = 1 ∧ (q : ℂ) = halfPlaneToCayley (ξ : ℂ) ∧
        (e q : ℂ) = halfPlaneToCayley (graphMap (pastedFareyHeight levels) x) := by
  let h := pastedFareyHeight levels
  let D := halfPlaneToCayley '' upperGraphDomain h
  let g := halfPlaneToCayley (graphMap h x)
  have h0 : ∀ t, 0 ≤ h t := pastedFareyHeight_nonneg levels
  have hh : Continuous h := pastedFareyHeight_continuous levels
  have hDopen : IsOpen D := by
    apply cayleyPartialHomeomorph.isOpen_image_of_subset_source (upperGraphDomain_isOpen hh)
    intro z hz
    change z + Complex.I ≠ 0
    exact add_I_ne_zero_of_im_pos ((h0 z.re).trans_lt hz)
  have hgfront : g ∈ frontier D := by
    rw [frontier_compactGraphDomain hh h0]
    exact Or.inr ⟨x, rfl⟩
  have hgnot : g ∉ D := by
    have hg := hgfront
    rw [hDopen.frontier_eq] at hg
    exact hg.2
  let gcl : closure D := ⟨g, frontier_subset_closure hgfront⟩
  let q : closedBall (0 : ℂ) 1 := e.symm gcl
  have hqimage : (e q : ℂ) = g := by
    have h := congrArg Subtype.val (e.apply_symm_apply gcl)
    exact h
  have hqnot : (q : ℂ) ∉ ball (0 : ℂ) 1 := by
    intro hq
    have hdom : (e q : ℂ) ∈ D := by
      rw [he q hq]
      refine ⟨Φ (cayleyToHalfPlane q), ?_, rfl⟩
      rw [← hΦimage]
      exact ⟨cayleyToHalfPlane q, cayleyToHalfPlane_im_pos hq, rfl⟩
    rw [hqimage] at hdom
    exact hgnot hdom
  have hqnorm : ‖(q : ℂ)‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp q.2)
    (le_of_not_gt fun hn => hqnot (mem_ball_zero_iff.mpr hn))
  have hqne : (q : ℂ) ≠ 1 := by
    intro hq1
    have hqeq : q = ⟨1, by simp⟩ := Subtype.ext hq1
    rw [hqeq, he1] at hqimage
    exact compactGraph_ne_one h0 x hqimage.symm
  have him : (cayleyToHalfPlane q).im = 0 := by
    rw [cayleyToHalfPlane_im, hqnorm]
    simp
  let ξ : ℝ := (cayleyToHalfPlane q).re
  have hreal : cayleyToHalfPlane q = (ξ : ℂ) := by
    apply Complex.ext
    · simp [ξ]
    · simp [him]
  have hqrep : (q : ℂ) = halfPlaneToCayley (ξ : ℂ) := by
    calc
      (q : ℂ) = halfPlaneToCayley (cayleyToHalfPlane q) :=
        (halfPlaneToCayley_cayleyToHalfPlane_of_ne_one hqne).symm
      _ = halfPlaneToCayley (ξ : ℂ) := congrArg halfPlaneToCayley hreal
  refine ⟨ξ, ⟨q, hqnorm, hqrep, hqimage⟩, ?_⟩
  intro ξ' hξ'
  obtain ⟨q', _hqnorm, hq'rep, hq'image⟩ := hξ'
  have hqeq : q' = q := e.injective (Subtype.ext (hq'image.trans hqimage.symm))
  have hceq : halfPlaneToCayley (ξ' : ℂ) = halfPlaneToCayley (ξ : ℂ) := by
    rw [← hq'rep, hqeq, hqrep]
  have hden (t : ℝ) : (t : ℂ) + Complex.I ≠ 0 := by
    intro ht
    have hi := congrArg Complex.im ht
    simp at hi
  have hrealEq := halfPlaneToCayley_injective_of_denominators (hden ξ') (hden ξ) hceq
  exact Complex.ofReal_injective hrealEq

end ThreeOmittedValues
