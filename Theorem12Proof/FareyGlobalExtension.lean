module

public import Theorem12Proof.FareyCuspFullLimit
public import Theorem12Proof.FareyPuncturedOmission
public import Theorem12Proof.CuspMeromorphicGerm
import Mathlib.Tactic

/-!
# The global meromorphic extension

The reflected modular composite is analytic away from isolated cusp
preimages and meromorphic at the cusps. Its canonical normal form gives a
single globally meromorphic function, with the usual default value at poles.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set Filter NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold Topology

namespace ThreeOmittedValues

theorem fareyReflected_meromorphicOn {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) :
    MeromorphicOn (fareyReflectedComposite e) Set.univ := by
  intro z _
  by_cases hz : z.im = 0
  · have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
    rw [hzreal]
    by_cases hv : (halfPlaneContinuousExtension e (z.re : ℂ)).im = 0
    · obtain ⟨k, hlim⟩ := fareyReflected_normalized_cusp_limit hupper hΦimage e he he1 z.re hv
      obtain ⟨r, hr, hdiff, homit⟩ := fareyReflected_punctured_omission hupper hΦ hΦimage e he he1 z.re
      have hzero : ∀ w ∈ ball (z.re : ℂ) r \ {(z.re : ℂ)}, fareyReflectedComposite e w ≠ 0 :=
        fun w hw => (homit w hw).1
      obtain ⟨G, hG, _, heq⟩ := cusp_normalization_has_meromorphic_germ k hr hdiff hzero hlim
      exact hG.meromorphicAt.congr heq
    · obtain ⟨u, hu⟩ := halfPlaneContinuousExtension_boundary hΦimage e he he1 (z := (z.re : ℂ)) (by simp)
      have hn : 0 ≤ (halfPlaneContinuousExtension e (z.re : ℂ)).im := by
        rw [hu]
        simpa [graphMap] using pastedFareyHeight_nonneg levels u
      have hp : 0 < (halfPlaneContinuousExtension e (z.re : ℂ)).im := lt_of_le_of_ne hn (Ne.symm hv)
      obtain ⟨r, hr, hdiff, _⟩ := farey_reflection_at_open_edge hupper hΦ hΦimage e he he1 z.re hp
      exact ((hdiff.analyticOnNhd isOpen_ball) _ (mem_ball_self hr)).meromorphicAt
  · let U : Set ℂ := {w : ℂ | w.im ≠ 0}
    have hopen : IsOpen U := isOpen_ne.preimage Complex.continuous_im
    have hdiff : DifferentiableOn ℂ (fareyReflectedComposite e) U := by
      intro w hw
      exact (fareyReflected_differentiableAt_off_real hupper hΦ hΦimage e he hw).differentiableWithinAt
    exact ((hdiff.analyticOnNhd hopen) z hz).meromorphicAt

noncomputable def fareyGlobalExtension {levels : ℤ → ℕ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels))) : ℂ → ℂ :=
  toMeromorphicNFOn (fareyReflectedComposite e) Set.univ

theorem fareyGlobalExtension_normalForm {levels : ℤ → ℕ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels))) :
    MeromorphicNFOn (fareyGlobalExtension e) Set.univ := by
  exact meromorphicNFOn_toMeromorphicNFOn _ _

theorem fareyGlobalExtension_eventuallyEq {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (z : ℂ) :
    fareyGlobalExtension e =ᶠ[𝓝[≠] z] fareyReflectedComposite e := by
  exact (fareyReflected_meromorphicOn hupper hΦ hΦimage e he he1).toMeromorphicNFOn_eq_self_on_nhdsNE (by simp)

theorem fareyGlobalExtension_eq_of_analytic {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (z : ℂ)
    (ha : AnalyticAt ℂ (fareyReflectedComposite e) z) :
    fareyGlobalExtension e z = fareyReflectedComposite e z := by
  have hNF := fareyGlobalExtension_normalForm e (show z ∈ Set.univ by simp)
  have heq := fareyGlobalExtension_eventuallyEq hupper hΦ hΦimage e he he1 z
  exact ((hNF.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds ha.meromorphicNFAt).mp heq).eq_of_nhds

end ThreeOmittedValues
