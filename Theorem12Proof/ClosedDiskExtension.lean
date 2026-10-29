/-
Adapted from RequestProject/RiemannMappingCaratheodory.lean in Quanyu Tang
and collaborators' Apache-2.0 Neumann development, commit
b37a190b8afc6efb128f204176d26deec8d88a8c. The results below use an
explicitly supplied boundary-limit theorem instead of a Lipschitz-domain
assumption.
-/
module

public import Theorem12Proof.RequestProject.RiemannMappingInterior
public import Mathlib.Topology.ExtendFrom
import Mathlib.Tactic

/-!
# Continuous extension from actual disk boundary limits

No boundary injectivity is assumed or proved here.
-/

@[expose] public section

open Set Metric Filter
open scoped Topology

namespace ThreeOmittedValues

noncomputable def diskExtension (F : ℂ → ℂ) : ℂ → ℂ :=
  extendFrom (ball (0 : ℂ) 1) F

theorem diskExtension_eqOn (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    EqOn (diskExtension F) F (ball (0 : ℂ) 1) := by
  intro z hz
  exact extendFrom_extends hF.continuousOn z hz

theorem diskExtension_exists_limit {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ p : ℂ,
      p ∈ frontier (F '' ball (0 : ℂ) 1) ∧
        Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    ∃ p : ℂ, Tendsto F (𝓝[ball (0 : ℂ) 1] z) (𝓝 p) := by
  have hn : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  rcases eq_or_lt_of_le hn with hn | hn
  · obtain ⟨p, _, hp⟩ := hboundary z hn
    exact ⟨p, hp⟩
  · exact ⟨F z, hF.continuousOn z (mem_ball_zero_iff.mpr hn)⟩

theorem diskExtension_continuousOn {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ p : ℂ,
      p ∈ frontier (F '' ball (0 : ℂ) 1) ∧
        Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p)) :
    ContinuousOn (diskExtension F) (closedBall (0 : ℂ) 1) := by
  apply continuousOn_extendFrom
  · rw [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)]
  · intro z hz
    exact diskExtension_exists_limit hF hboundary hz

theorem diskExtension_mem_frontier {F : ℂ → ℂ}
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ p : ℂ,
      p ∈ frontier (F '' ball (0 : ℂ) 1) ∧
        Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) : diskExtension F ζ ∈ frontier (F '' ball (0 : ℂ) 1) := by
  obtain ⟨p, hp, hlim⟩ := hboundary ζ hζ
  have hζcl : ζ ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0), mem_closedBall_zero_iff, hζ]
  have he : diskExtension F ζ = p := extendFrom_eq hζcl hlim
  exact he.symm ▸ hp

theorem closedDisk_image_eq_closure_of_continuousOn (G : ℂ → ℂ)
    (hG : ContinuousOn G (closedBall (0 : ℂ) 1)) :
    G '' closedBall (0 : ℂ) 1 = closure (G '' ball (0 : ℂ) 1) := by
  have hcl : closure (ball (0 : ℂ) 1) = closedBall (0 : ℂ) 1 :=
    closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)
  have hGc : ContinuousOn G (closure (ball (0 : ℂ) 1)) := by
    simpa only [hcl] using hG
  apply Subset.antisymm
  · simpa only [hcl] using hGc.image_closure
  · apply closure_minimal
    · rintro w ⟨z, hz, rfl⟩
      exact ⟨z, ball_subset_closedBall hz, rfl⟩
    · exact ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hG).isClosed

theorem diskExtension_closed_image {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ p : ℂ,
      p ∈ frontier (F '' ball (0 : ℂ) 1) ∧
        Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p)) :
    diskExtension F '' closedBall (0 : ℂ) 1 = closure (F '' ball (0 : ℂ) 1) := by
  rw [closedDisk_image_eq_closure_of_continuousOn _ (diskExtension_continuousOn hF hboundary),
    (diskExtension_eqOn F hF).image_eq]

theorem diskExtension_sphere_image {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ p : ℂ,
      p ∈ frontier (F '' ball (0 : ℂ) 1) ∧
        Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p)) :
    diskExtension F '' sphere (0 : ℂ) 1 = frontier (F '' ball (0 : ℂ) 1) := by
  have hopen : IsOpen (F '' ball (0 : ℂ) 1) :=
    PolyaNeumann.RiemannInterior.isOpen_image_of_injOn isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
      hF hinj Subset.rfl isOpen_ball
  apply Subset.antisymm
  · rintro w ⟨ζ, hζ, rfl⟩
    exact diskExtension_mem_frontier hboundary (by simpa only [mem_sphere, dist_zero_right] using hζ)
  · intro w hw
    have hwcl := frontier_subset_closure hw
    rw [← diskExtension_closed_image hF hboundary] at hwcl
    obtain ⟨z, hz, he⟩ := hwcl
    refine ⟨z, ?_, he⟩
    have hn : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    rcases eq_or_lt_of_le hn with hn | hn
    · simpa only [mem_sphere, dist_zero_right] using hn
    · have hzD : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hn
      have hwΩ : w ∈ F '' ball (0 : ℂ) 1 :=
        ⟨z, hzD, (diskExtension_eqOn F hF hzD).symm.trans he⟩
      rw [hopen.frontier_eq] at hw
      exact False.elim (hw.2 hwΩ)

end ThreeOmittedValues
