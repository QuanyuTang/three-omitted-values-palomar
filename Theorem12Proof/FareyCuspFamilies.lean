module

public import Theorem12Proof.FareyBoundaryVertices
public import Theorem12Proof.FareyCuspFullLimit
public import Theorem12Proof.CuspThreeFamilies
import Mathlib.Tactic

/-!
# Explicit boundary cusp families

The boundary correspondence reaches every finite graph point. Evaluating
the three modular cusp matrices there produces three sequences of distinct
real parameters with zero, one, and pole cusp limits.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set Filter NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold Topology

namespace ThreeOmittedValues

theorem farey_graph_has_real_parameter {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (r : ℝ) :
    ∃ x : ℝ, halfPlaneContinuousExtension e (x : ℂ) = graphMap (pastedFareyHeight levels) r := by
  obtain ⟨x, ⟨q, _hqnorm, hq, heq⟩, _⟩ := unique_real_boundary_parameter hΦimage e he he1 r
  refine ⟨x, ?_⟩
  have hq' : closedHalfPlaneCayley ⟨(x : ℂ), by simp⟩ = q := by
    apply Subtype.ext
    simpa [closedHalfPlaneCayley] using hq.symm
  have hnonneg : 0 ≤ (graphMap (pastedFareyHeight levels) r).im := by
    simpa [graphMap] using pastedFareyHeight_nonneg levels r
  calc
    halfPlaneContinuousExtension e (x : ℂ) = cayleyToHalfPlane (e q) := by
      simp [halfPlaneContinuousExtension, closedHalfPlaneMap, hq']
    _ = cayleyToHalfPlane (halfPlaneToCayley (graphMap (pastedFareyHeight levels) r)) := by rw [heq]
    _ = graphMap (pastedFareyHeight levels) r :=
      cayleyToHalfPlane_halfPlaneToCayley_of_denominator (add_I_ne_zero_of_im_nonneg hnonneg)

theorem fareyReflected_cusp_limit_of_matrix {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x r : ℝ)
    (hr0 : pastedFareyHeight levels r = 0)
    (hrval : halfPlaneContinuousExtension e (x : ℂ) = (r : ℂ))
    (γ : SL(2, ℤ)) (p q : ℤ) (hq : 0 < q) (hr : r = (p : ℝ) / q)
    (h00 : γ.1 0 0 = p) (h10 : γ.1 1 0 = q) (k : Fin 6)
    (hk : ∀ τ : UpperHalfPlane,
      modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ) = lambdaTransform k (modularLambdaH (τ : ℂ))) :
    Tendsto (fun z => cuspNormalize k (fareyReflectedComposite e z))
      (𝓝[≠] (x : ℂ)) (𝓝 0) := by
  apply fareyReflected_normalized_cusp_limit_of_closed e x k
  exact farey_normalized_cusp_limit_closed_of_matrix hupper hΦimage e he he1 x r hr0 hrval
    γ p q hq hr h00 h10 k hk

theorem farey_three_cusp_families {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hlevels : ∀ n, 1 ≤ levels n)
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (n : ℤ) :
    (∃ x : ℝ, halfPlaneContinuousExtension e (x : ℂ) = ((((2 * n : ℤ) : ℝ) + 1 / 2 : ℝ) : ℂ) ∧
      Tendsto (fareyReflectedComposite e) (𝓝[≠] (x : ℂ)) (𝓝 0)) ∧
    (∃ x : ℝ, halfPlaneContinuousExtension e (x : ℂ) = (((2 * n : ℤ) : ℂ)) ∧
      Tendsto (fun z => 1 - fareyReflectedComposite e z) (𝓝[≠] (x : ℂ)) (𝓝 0)) ∧
    (∃ x : ℝ, halfPlaneContinuousExtension e (x : ℂ) = (((2 * n + 1 : ℤ) : ℂ)) ∧
      Tendsto (fun z => (fareyReflectedComposite e z)⁻¹) (𝓝[≠] (x : ℂ)) (𝓝 0)) := by
  have hz0 := pastedFareyHeight_half_int levels (2 * n) (hlevels (2 * n))
  have ho0 := pastedFareyHeight_int levels (2 * n)
  have hp0 := pastedFareyHeight_int levels (2 * n + 1)
  obtain ⟨xz, hxz⟩ := farey_graph_has_real_parameter hΦimage e he he1 (((2 * n : ℤ) : ℝ) + 1 / 2)
  obtain ⟨xo, hxo⟩ := farey_graph_has_real_parameter hΦimage e he he1 (((2 * n : ℤ) : ℝ))
  obtain ⟨xp, hxp⟩ := farey_graph_has_real_parameter hΦimage e he he1 (((2 * n + 1 : ℤ) : ℝ))
  have hgraph (r : ℝ) (hr : pastedFareyHeight levels r = 0) :
      graphMap (pastedFareyHeight levels) r = (r : ℂ) := by
    apply Complex.ext <;> simp [graphMap, hr]
  have hxz' : halfPlaneContinuousExtension e (xz : ℂ) = ((((2 * n : ℤ) : ℝ) + 1 / 2 : ℝ) : ℂ) :=
    hxz.trans (hgraph _ hz0)
  have hxo' : halfPlaneContinuousExtension e (xo : ℂ) = ((((2 * n : ℤ) : ℝ)) : ℂ) :=
    hxo.trans (hgraph _ ho0)
  have hxp' : halfPlaneContinuousExtension e (xp : ℂ) = ((((2 * n + 1 : ℤ) : ℝ)) : ℂ) :=
    hxp.trans (hgraph _ hp0)
  refine ⟨⟨xz, hxz', ?_⟩, ⟨xo, ?_, ?_⟩, ⟨xp, ?_, ?_⟩⟩
  · have hr : (((2 * n : ℤ) : ℝ) + 1 / 2) = ((4 * n + 1 : ℤ) : ℝ) / (2 : ℤ) := by
      push_cast; ring
    have hc := zeroCuspMatrix_first_column n
    simpa [cuspNormalize] using fareyReflected_cusp_limit_of_matrix hupper hΦimage e he he1 xz _ hz0 hxz'
      (zeroCuspMatrix n) (4 * n + 1) 2 (by norm_num) hr hc.1 hc.2 0 (zeroCuspMatrix_formula n)
  · simpa using hxo'
  · have hc := oneCuspMatrix_first_column n
    have hr : (((2 * n : ℤ) : ℝ)) = ((2 * n : ℤ) : ℝ) / (1 : ℤ) := by simp
    simpa [cuspNormalize] using fareyReflected_cusp_limit_of_matrix hupper hΦimage e he he1 xo _ ho0 hxo'
      (oneCuspMatrix n) (2 * n) 1 (by norm_num) hr hc.1 hc.2 1 (oneCuspMatrix_formula n)
  · simpa using hxp'
  · have hc := poleCuspMatrix_first_column n
    have hr : (((2 * n + 1 : ℤ) : ℝ)) = ((2 * n + 1 : ℤ) : ℝ) / (1 : ℤ) := by simp
    simpa [cuspNormalize] using fareyReflected_cusp_limit_of_matrix hupper hΦimage e he he1 xp _ hp0 hxp'
      (poleCuspMatrix n) (2 * n + 1) 1 (by norm_num) hr hc.1 hc.2 4 (poleCuspMatrix_formula n)

end ThreeOmittedValues
