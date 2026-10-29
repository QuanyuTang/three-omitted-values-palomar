module

public import Theorem12Proof.FareyBoundaryVerticesDiscrete
public import Theorem12Proof.FareyEdgeReflection
import Mathlib.Tactic

/-!
# Holomorphy in punctured neighborhoods of Farey vertices

The reflected composite is analytic on both open half-planes and across each
open edge. Local finiteness of the vertex preimages then supplies a punctured
disk around every real boundary point on which it is holomorphic.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem fareyReflected_differentiableAt_off_real {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    {z : ℂ} (hz : z.im ≠ 0) : DifferentiableAt ℂ (fareyReflectedComposite e) z := by
  let H : Set ℂ := {z : ℂ | 0 < z.im}
  let f : ℂ → ℂ := fun w => modularLambdaH (halfPlaneContinuousExtension e w)
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hΦmaps : MapsTo Φ H H := by
    intro w hw
    apply hupper
    rw [← hΦimage]
    exact ⟨w, hw, rfl⟩
  have hcomp : DifferentiableOn ℂ (fun w => modularLambdaH (Φ w)) H :=
    modularLambdaH_differentiableOn.comp hΦ hΦmaps
  have hf_at (w : ℂ) (hw : 0 < w.im) : DifferentiableAt ℂ f w := by
    apply (hcomp.differentiableAt (hH.mem_nhds hw)).congr_of_eventuallyEq
    filter_upwards [hH.mem_nhds hw] with v hv
    exact congrArg modularLambdaH (halfPlaneContinuousExtension_interior hupper hΦimage e he hv)
  by_cases hp : 0 < z.im
  · exact schwarzReflect_differentiableAt_of_im_pos hp (hf_at z hp)
  · have hn : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
    have hconj : 0 < ((starRingEnd ℂ) z).im := by simp; linarith
    exact schwarzReflect_differentiableAt_of_im_neg hn (hf_at _ hconj)

theorem fareyReflected_punctured_holomorphic {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ) :
    ∃ r : ℝ, 0 < r ∧ DifferentiableOn ℂ (fareyReflectedComposite e)
      (ball (x : ℂ) r \ {(x : ℂ)}) := by
  obtain ⟨r, hr, hisol⟩ := farey_preimage_vertex_isolated hΦimage e he he1 x
  refine ⟨r, hr, ?_⟩
  intro z hz
  by_cases hzim : z.im = 0
  · have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hzim]
    have hreball : z.re ∈ ball x r := by
      have hdist : ‖z - (x : ℂ)‖ < r := by simpa [mem_ball, dist_eq_norm] using hz.1
      have h := (Complex.abs_re_le_norm (z - (x : ℂ))).trans_lt hdist
      simpa [mem_ball, Real.dist_eq] using h
    have hbar_ne : (halfPlaneContinuousExtension e z).im ≠ 0 := by
      intro hzero
      have hzero' : (halfPlaneContinuousExtension e (z.re : ℂ)).im = 0 := by
        rw [← hzreal]
        exact hzero
      have hxr : z.re = x := hisol z.re hreball hzero'
      have hzeq : z = (x : ℂ) := by rw [hzreal, hxr]
      exact hz.2 (by simpa [hzeq])
    obtain ⟨u, hu⟩ := halfPlaneContinuousExtension_boundary hΦimage e he he1 hzim
    have hbar_nonneg : 0 ≤ (halfPlaneContinuousExtension e z).im := by
      rw [hu]
      simpa [graphMap] using pastedFareyHeight_nonneg levels u
    have hbar_pos : 0 < (halfPlaneContinuousExtension e z).im :=
      lt_of_le_of_ne hbar_nonneg (Ne.symm hbar_ne)
    have hbar_pos' : 0 < (halfPlaneContinuousExtension e (z.re : ℂ)).im := by
      rw [← hzreal]
      exact hbar_pos
    obtain ⟨s, hs, hdiff, _⟩ := farey_reflection_at_open_edge hupper hΦ hΦimage e he he1 z.re hbar_pos'
    have hdiffat := hdiff.differentiableAt (ball_mem_nhds (z.re : ℂ) hs)
    rw [← hzreal] at hdiffat
    exact hdiffat.differentiableWithinAt
  · exact (fareyReflected_differentiableAt_off_real hupper hΦ hΦimage e he hzim).differentiableWithinAt

end ThreeOmittedValues
