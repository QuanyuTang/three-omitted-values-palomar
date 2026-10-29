module

public import Theorem12Proof.FareyCompactJordan
public import Theorem12Proof.CompactGraphFrontier
public import Theorem12Proof.RectifiableBoundaryLimit
import Mathlib.Tactic

/-!
# Boundary limits for the Farey-domain Riemann map

After Cayley compactification, the actual Farey frontier is the rectifiable
Jordan curve already constructed. The small-cap theorem therefore gives a
unique full interior limit at each disk boundary point. Boundary
injectivity and normalization at infinity remain to be proved.
-/

@[expose] public section

open Complex Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem compact_farey_riemann_map_boundary_limit (levels : ℤ → ℕ) (G : ℂ → ℂ)
    (hG : DifferentiableOn ℂ G (ball (0 : ℂ) 1))
    (hGinj : InjOn G (ball (0 : ℂ) 1))
    (hGimage : G '' ball (0 : ℂ) 1 = upperGraphDomain (pastedFareyHeight levels))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃! p : ℂ,
      p ∈ frontier (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)) ∧
      Tendsto (halfPlaneToCayley ∘ G) (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p) := by
  let h := pastedFareyHeight levels
  have h0 : ∀ x, 0 ≤ h x := pastedFareyHeight_nonneg levels
  have hGmem (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : G z ∈ upperGraphDomain h := by
    rw [← hGimage]
    exact ⟨z, hz, rfl⟩
  have hGpos (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : 0 < (G z).im :=
    (h0 (G z).re).trans_lt (hGmem z hz)
  have hF : DifferentiableOn ℂ (halfPlaneToCayley ∘ G) (ball (0 : ℂ) 1) := by
    intro z hz
    have hden : G z + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos (hGpos z hz)
    have hc : DifferentiableAt ℂ halfPlaneToCayley (G z) := by
      unfold halfPlaneToCayley
      fun_prop (disch := exact hden)
    exact hc.comp_differentiableWithinAt z (hG z hz)
  have hFinj : InjOn (halfPlaneToCayley ∘ G) (ball (0 : ℂ) 1) := by
    intro z hz w hw heq
    apply hGinj hz hw
    exact halfPlaneToCayley_injective_of_denominators
      (add_I_ne_zero_of_im_pos (hGpos z hz)) (add_I_ne_zero_of_im_pos (hGpos w hw)) heq
  have hFimage : (halfPlaneToCayley ∘ G) '' ball (0 : ℂ) 1 =
      halfPlaneToCayley '' upperGraphDomain h := by
    rw [Set.image_comp, hGimage]
  have hFbounded : Bornology.IsBounded ((halfPlaneToCayley ∘ G) '' ball (0 : ℂ) 1) := by
    apply Metric.isBounded_ball.subset
    rintro _ ⟨z, hz, rfl⟩
    exact halfPlaneToCayley_mem_ball (hGpos z hz)
  obtain ⟨γ, ⟨K, hK⟩, hper, hγinj, hγimage⟩ :=
    exists_periodic_lipschitz_compactFareyGraph levels
  have himage : γ '' Icc 0 (2 * Real.pi) =
      frontier ((halfPlaneToCayley ∘ G) '' ball (0 : ℂ) 1) := by
    rw [hFimage, frontier_compactGraphDomain (pastedFareyHeight_continuous levels) h0]
    exact hγimage
  have hlimit := boundary_limit_of_lipschitz_jordan_frontier (halfPlaneToCayley ∘ G)
    hF hFinj hFbounded hK hper hγinj himage hζ
  simpa only [hFimage] using hlimit

end ThreeOmittedValues
