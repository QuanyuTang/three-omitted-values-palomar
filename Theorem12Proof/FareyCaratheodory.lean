module

public import Theorem12Proof.FareyBoundaryLimit
public import Theorem12Proof.CompactGraphNeighborhoods
public import Theorem12Proof.DiskExtensionInjective
public import Theorem12Proof.FareyDomain
import Mathlib.Tactic

/-!
# Closed-disk homeomorphism for the actual Farey domain

The Riemann map's compactification extends to a homeomorphism of the closed
disk. Normalization of the map, modular reflection, and the comparison-domain
and non-Blaschke arguments remain separate obligations.
-/

@[expose] public section

open Complex Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem compact_farey_riemann_map_closedDisk_homeomorph (levels : ℤ → ℕ) (G : ℂ → ℂ)
    (hG : DifferentiableOn ℂ G (ball (0 : ℂ) 1))
    (hGinj : InjOn G (ball (0 : ℂ) 1))
    (hGimage : G '' ball (0 : ℂ) 1 = upperGraphDomain (pastedFareyHeight levels)) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ
        closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)),
      ∀ z : closedBall (0 : ℂ) 1, (e z : ℂ) = diskExtension (halfPlaneToCayley ∘ G) z := by
  let h := pastedFareyHeight levels
  let F := halfPlaneToCayley ∘ G
  have h0 : ∀ x, 0 ≤ h x := pastedFareyHeight_nonneg levels
  have hGmem (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : G z ∈ upperGraphDomain h := by
    rw [← hGimage]
    exact ⟨z, hz, rfl⟩
  have hGpos (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : 0 < (G z).im :=
    (h0 (G z).re).trans_lt (hGmem z hz)
  have hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1) := by
    intro z hz
    have hden : G z + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos (hGpos z hz)
    have hc : DifferentiableAt ℂ halfPlaneToCayley (G z) := by
      unfold halfPlaneToCayley
      fun_prop (disch := exact hden)
    exact hc.comp_differentiableWithinAt z (hG z hz)
  have hFinj : InjOn F (ball (0 : ℂ) 1) := by
    intro z hz w hw heq
    apply hGinj hz hw
    exact halfPlaneToCayley_injective_of_denominators
      (add_I_ne_zero_of_im_pos (hGpos z hz)) (add_I_ne_zero_of_im_pos (hGpos w hw)) heq
  have hFimage : F '' ball (0 : ℂ) 1 = halfPlaneToCayley '' upperGraphDomain h := by
    rw [Set.image_comp, hGimage]
  have hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ p : ℂ,
      p ∈ frontier (F '' ball (0 : ℂ) 1) ∧ Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p) := by
    intro ζ hζ
    obtain ⟨p, hp, _⟩ := compact_farey_riemann_map_boundary_limit levels G hG hGinj hGimage hζ
    refine ⟨p, ?_⟩
    simpa only [hFimage] using hp
  have hlocal : ConnectedBoundaryNeighborhoods (F '' ball (0 : ℂ) 1) := by
    rw [hFimage]
    exact compactGraphDomain_connectedBoundaryNeighborhoods (pastedFareyHeight_continuous levels) h0
  have he := diskExtension_homeomorph_of_connected_neighborhoods hF hFinj hboundary hlocal
  rw [hFimage] at he
  simpa only [F] using! he

/-- The graph and interior map from the main construction also have the
proved closed-disk homeomorphism after Cayley compactification. -/
theorem exists_farey_domain_with_closedDisk_homeomorph (β : ℝ → ℝ)
    (hβcont : Continuous β) (hβpos : ∀ x, 0 < β x) :
    ∃ (levels : ℤ → ℕ) (G : ℂ → ℂ),
      (∀ n, 1 ≤ levels n) ∧
      (∀ x, 0 ≤ pastedFareyHeight levels x ∧ pastedFareyHeight levels x < β x) ∧
      (∀ n : ℤ, pastedFareyHeight levels (n : ℝ) = 0 ∧
        pastedFareyHeight levels ((n : ℝ) + 1 / 2) = 0) ∧
      IsProperMap (graphMap (pastedFareyHeight levels)) ∧
      globalFareyArcs levels = Set.range (graphMap (pastedFareyHeight levels)) ∧
      IsOpen (upperGraphDomain (pastedFareyHeight levels)) ∧
      SimplyConnectedSpace (upperGraphDomain (pastedFareyHeight levels)) ∧
      upperGraphDomain β ⊆ upperGraphDomain (pastedFareyHeight levels) ∧
      upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ G (ball (0 : ℂ) 1) ∧ InjOn G (ball (0 : ℂ) 1) ∧
      G '' ball (0 : ℂ) 1 = upperGraphDomain (pastedFareyHeight levels) ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ
          closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)),
        ∀ z : closedBall (0 : ℂ) 1, (e z : ℂ) = diskExtension (halfPlaneToCayley ∘ G) z := by
  obtain ⟨levels, G, hlevels, hbelow, hvertices, hproper, harcs, hopen, hsc,
    hsubset, hupper, hG, hGinj, hGimage⟩ := exists_farey_domain_with_interior_map β hβcont hβpos
  exact ⟨levels, G, hlevels, hbelow, hvertices, hproper, harcs, hopen, hsc,
    hsubset, hupper, hG, hGinj, hGimage,
    compact_farey_riemann_map_closedDisk_homeomorph levels G hG hGinj hGimage⟩

end ThreeOmittedValues
