module

public import Theorem12Proof.FareyGlobalExtension
public import Theorem12Proof.MeromorphicFibres
import Mathlib.Tactic

/-!
# Analyticity, omission, and real symmetry of the global extension
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set Filter NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold Topology

namespace ThreeOmittedValues

theorem fareyGlobalExtension_off_real {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ (fareyGlobalExtension e) z ∧
      fareyGlobalExtension e z = fareyReflectedComposite e z ∧
      fareyGlobalExtension e z ≠ 0 ∧ fareyGlobalExtension e z ≠ 1 := by
  let U : Set ℂ := {w : ℂ | w.im ≠ 0}
  have hopen : IsOpen U := isOpen_ne.preimage Complex.continuous_im
  have hdiff : DifferentiableOn ℂ (fareyReflectedComposite e) U := by
    intro w hw
    exact (fareyReflected_differentiableAt_off_real hupper hΦ hΦimage e he hw).differentiableWithinAt
  have hR : AnalyticAt ℂ (fareyReflectedComposite e) z := (hdiff.analyticOnNhd hopen) z hz
  have hNF := fareyGlobalExtension_normalForm e (show z ∈ Set.univ by simp)
  have heq := (hNF.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hR.meromorphicNFAt).mp
    (fareyGlobalExtension_eventuallyEq hupper hΦ hΦimage e he he1 z)
  have ha : AnalyticAt ℂ (fareyGlobalExtension e) z := (analyticAt_congr heq).mpr hR
  have heqz := heq.eq_of_nhds
  have homit := fareyReflected_omits_of_nonvertex hupper hΦimage e he (z := z) (fun h => (hz h).elim)
  exact ⟨ha, heqz, by simpa [heqz] using homit.1, by simpa [heqz] using homit.2⟩

theorem fareyGlobalExtension_upper {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) {z : ℂ} (hz : 0 < z.im) :
    fareyGlobalExtension e z = modularLambdaH (Φ z) := by
  rw [(fareyGlobalExtension_off_real hupper hΦ hΦimage e he he1 hz.ne').2.1,
    fareyReflectedComposite, schwarzReflect_apply_of_im_nonneg _ hz.le,
    halfPlaneContinuousExtension_interior hupper hΦimage e he hz]

theorem fareyGlobalExtension_vertex_value {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ)
    (hx : (halfPlaneContinuousExtension e (x : ℂ)).im = 0) :
    fareyGlobalExtension e (x : ℂ) = 0 ∨ fareyGlobalExtension e (x : ℂ) = 1 := by
  obtain ⟨k, hlim⟩ := fareyReflected_normalized_cusp_limit hupper hΦimage e he he1 x hx
  obtain ⟨r, hr, hdiff, homit⟩ := fareyReflected_punctured_omission hupper hΦ hΦimage e he he1 x
  obtain ⟨G, hG, hval, hGeq⟩ := cusp_normalization_has_meromorphic_germ k hr hdiff
    (fun z hz => (homit z hz).1) hlim
  have hNF := fareyGlobalExtension_normalForm e (show (x : ℂ) ∈ Set.univ by simp)
  have heq : fareyGlobalExtension e =ᶠ[𝓝[≠] (x : ℂ)] G :=
    (fareyGlobalExtension_eventuallyEq hupper hΦ hΦimage e he he1 (x : ℂ)).trans hGeq.symm
  have hsame := ((hNF.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hG).mp heq).eq_of_nhds
  simpa [hsame] using hval

theorem fareyGlobalExtension_real_axis {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ) :
    (fareyGlobalExtension e (x : ℂ)).im = 0 := by
  by_cases hv : (halfPlaneContinuousExtension e (x : ℂ)).im = 0
  · rcases fareyGlobalExtension_vertex_value hupper hΦ hΦimage e he he1 x hv with h | h <;> simp [h]
  · obtain ⟨u, hu⟩ := halfPlaneContinuousExtension_boundary hΦimage e he he1 (z := (x : ℂ)) (by simp)
    have hn : 0 ≤ (halfPlaneContinuousExtension e (x : ℂ)).im := by
      rw [hu]
      simpa [graphMap] using pastedFareyHeight_nonneg levels u
    have hp : 0 < (halfPlaneContinuousExtension e (x : ℂ)).im := lt_of_le_of_ne hn (Ne.symm hv)
    obtain ⟨r, hr, hdiff, _⟩ := farey_reflection_at_open_edge hupper hΦ hΦimage e he he1 x hp
    have ha := (hdiff.analyticOnNhd isOpen_ball) (x : ℂ) (mem_ball_self hr)
    rw [fareyGlobalExtension_eq_of_analytic hupper hΦ hΦimage e he he1 _ ha,
      fareyReflectedComposite, schwarzReflect_apply_of_im_nonneg _ (by simp)]
    have hgraph : halfPlaneContinuousExtension e (x : ℂ) ∈ globalFareyArcs levels := by
      rw [globalFareyArcs_eq_graph, hu]
      simp [graphMap]
    exact modularLambdaH_real_on_globalFareyArcs levels hgraph hp

theorem fareyGlobalExtension_realSymmetric {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (z : ℂ) :
    fareyGlobalExtension e ((starRingEnd ℂ) z) = (starRingEnd ℂ) (fareyGlobalExtension e z) := by
  by_cases hz : z.im = 0
  · have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
    rw [hzreal]
    have hreal := fareyGlobalExtension_real_axis hupper hΦ hΦimage e he he1 z.re
    apply Complex.ext <;> simp [hreal]
  · have hc : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
    rw [(fareyGlobalExtension_off_real hupper hΦ hΦimage e he he1 hc).2.1,
      (fareyGlobalExtension_off_real hupper hΦ hΦimage e he he1 hz).2.1]
    by_cases hp : 0 < z.im
    · have hn : ((starRingEnd ℂ) z).im < 0 := by simp; linarith
      rw [fareyReflectedComposite, schwarzReflect_apply_of_im_neg _ hn,
        schwarzReflect_apply_of_im_nonneg _ hp.le]
      simp
    · have hn : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
      have hp' : 0 ≤ ((starRingEnd ℂ) z).im := by simp; linarith
      rw [fareyReflectedComposite, schwarzReflect_apply_of_im_nonneg _ hp',
        schwarzReflect_apply_of_im_neg _ hn]
      simp

end ThreeOmittedValues
