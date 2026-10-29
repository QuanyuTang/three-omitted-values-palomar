module

public import Theorem12Proof.FareyCuspBoundaryLimit
public import Theorem12Proof.FareyEdgeReflection
import Mathlib.Tactic

/-!
# Full punctured cusp limits of the reflected composite

Conjugation folds the lower half-plane onto the closed upper half-plane. The
three cusp normalizations have real coefficients, so the normalized limit is
preserved by Schwarz reflection.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set Filter NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold Topology

namespace ThreeOmittedValues

noncomputable def foldUpper (z : ℂ) : ℂ :=
  if 0 ≤ z.im then z else (starRingEnd ℂ) z

theorem foldUpper_dist_real (x : ℝ) (z : ℂ) : dist (foldUpper z) (x : ℂ) = dist z (x : ℂ) := by
  by_cases hz : 0 ≤ z.im
  · simp [foldUpper, hz]
  · have h := Complex.dist_conj_conj z (x : ℂ)
    simpa [foldUpper, hz] using h

theorem foldUpper_tendsto_punctured (x : ℝ) :
    Tendsto foldUpper (𝓝[≠] (x : ℂ)) (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [show ball (x : ℂ) ε ∈ 𝓝[≠] (x : ℂ) from
      nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hε)] with z hz
    simpa [mem_ball, foldUpper_dist_real] using hz
  · filter_upwards [eventually_mem_nhdsWithin] with z hz
    have hzneq : z ≠ (x : ℂ) := by simpa using hz
    have hfoldneq : foldUpper z ≠ (x : ℂ) := by
      intro heq
      have hd := foldUpper_dist_real x z
      rw [heq, dist_self] at hd
      exact hzneq (dist_eq_zero.mp hd.symm)
    refine ⟨?_, by simpa using hfoldneq⟩
    by_cases hzim : 0 ≤ z.im
    · simpa [foldUpper, hzim] using hzim
    · simp [foldUpper, hzim]
      linarith

theorem cuspNormalize_conj (k : Fin 6) (z : ℂ) :
    cuspNormalize k ((starRingEnd ℂ) z) = (starRingEnd ℂ) (cuspNormalize k z) := by
  fin_cases k <;> simp [cuspNormalize]

theorem fareyReflected_normalized_cusp_limit_of_closed {levels : ℤ → ℕ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels))) (x : ℝ) (k : Fin 6)
    (hk : Tendsto (fun z => cuspNormalize k
      (modularLambdaH (halfPlaneContinuousExtension e z)))
      (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ)) (𝓝 0)) :
    Tendsto (fun z => cuspNormalize k (fareyReflectedComposite e z))
      (𝓝[≠] (x : ℂ)) (𝓝 0) := by
  have hfold := foldUpper_tendsto_punctured x
  have hcomp := hk.comp hfold
  have hnorm : ∀ z : ℂ, ‖cuspNormalize k (fareyReflectedComposite e z)‖ =
      ‖cuspNormalize k (modularLambdaH (halfPlaneContinuousExtension e (foldUpper z)))‖ := by
    intro z
    by_cases hz : 0 ≤ z.im
    · simp [fareyReflectedComposite, schwarzReflect, foldUpper, hz]
    · simp [fareyReflectedComposite, schwarzReflect, foldUpper, hz, cuspNormalize_conj]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hn := (tendsto_zero_iff_norm_tendsto_zero.mp hcomp)
  apply hn.congr'
  filter_upwards [] with z
  exact (hnorm z).symm

theorem fareyReflected_normalized_cusp_limit {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ)
    (hxvertex : (halfPlaneContinuousExtension e (x : ℂ)).im = 0) :
    ∃ k : Fin 6, Tendsto (fun z => cuspNormalize k (fareyReflectedComposite e z))
      (𝓝[≠] (x : ℂ)) (𝓝 0) := by
  obtain ⟨k, hk⟩ := farey_normalized_cusp_limit_closed hupper hΦimage e he he1 x hxvertex
  exact ⟨k, fareyReflected_normalized_cusp_limit_of_closed e x k hk⟩

end ThreeOmittedValues
