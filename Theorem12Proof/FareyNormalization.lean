module

public import Theorem12Proof.FareyCaratheodory
public import Theorem12Proof.DiskNormalization
public import Theorem12Proof.ClosedDiskAutomorphisms
import Mathlib.Tactic

/-!
# Interior and boundary normalization of the Farey Riemann map

The disk center is sent to a prescribed point of the Farey domain, and the
boundary point `1` is sent to the compactified point at infinity. The
resulting closed-disk map is a homeomorphism.
-/

@[expose] public section

open Complex Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem exists_farey_map_normalized_at_point_and_infinity (levels : ℤ → ℕ)
    (G : ℂ → ℂ) (p : ℂ)
    (hG : DifferentiableOn ℂ G (ball (0 : ℂ) 1))
    (hGinj : InjOn G (ball (0 : ℂ) 1))
    (hGimage : G '' ball (0 : ℂ) 1 = upperGraphDomain (pastedFareyHeight levels))
    (hp : p ∈ upperGraphDomain (pastedFareyHeight levels)) :
    ∃ G₁ : ℂ → ℂ,
      DifferentiableOn ℂ G₁ (ball (0 : ℂ) 1) ∧
      InjOn G₁ (ball (0 : ℂ) 1) ∧
      G₁ '' ball (0 : ℂ) 1 = upperGraphDomain (pastedFareyHeight levels) ∧
      G₁ 0 = p ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ
          closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)),
        (∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
          (e z : ℂ) = halfPlaneToCayley (G₁ z)) ∧
        (e ⟨1, by simp⟩ : ℂ) = 1 := by
  obtain ⟨G₀, hG₀, hG₀inj, hG₀image, hG₀zero⟩ :=
    exists_disk_map_normalized_at hG hGinj hGimage hp
  let h := pastedFareyHeight levels
  let F₀ := halfPlaneToCayley ∘ G₀
  have h0 : ∀ x, 0 ≤ h x := pastedFareyHeight_nonneg levels
  have hG₀mem (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : G₀ z ∈ upperGraphDomain h := by
    rw [← hG₀image]
    exact ⟨z, hz, rfl⟩
  have hG₀pos (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : 0 < (G₀ z).im :=
    (h0 (G₀ z).re).trans_lt (hG₀mem z hz)
  have hF₀ : DifferentiableOn ℂ F₀ (ball (0 : ℂ) 1) := by
    intro z hz
    have hden : G₀ z + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos (hG₀pos z hz)
    have hc : DifferentiableAt ℂ halfPlaneToCayley (G₀ z) := by
      unfold halfPlaneToCayley
      fun_prop (disch := exact hden)
    exact hc.comp_differentiableWithinAt z (hG₀ z hz)
  obtain ⟨e₀, he₀⟩ := compact_farey_riemann_map_closedDisk_homeomorph
    levels G₀ hG₀ hG₀inj hG₀image
  have h1front : (1 : ℂ) ∈ frontier (halfPlaneToCayley '' upperGraphDomain h) :=
    one_mem_frontier_compactGraphDomain h0
  let yInf : closure (halfPlaneToCayley '' upperGraphDomain h) := ⟨1, frontier_subset_closure h1front⟩
  let η : closedBall (0 : ℂ) 1 := e₀.symm yInf
  have heη : (e₀ η : ℂ) = 1 := by
    have he := congrArg Subtype.val (e₀.apply_symm_apply yInf)
    exact he
  have hηnot : (η : ℂ) ∉ ball (0 : ℂ) 1 := by
    intro hηin
    have heF : F₀ η = 1 := by
      calc
        F₀ η = diskExtension F₀ η := (diskExtension_eqOn F₀ hF₀ hηin).symm
        _ = (e₀ η : ℂ) := (he₀ η).symm
        _ = 1 := heη
    have him : F₀ η ∈ ball (0 : ℂ) 1 := halfPlaneToCayley_mem_ball (hG₀pos η hηin)
    rw [heF] at him
    norm_num [mem_ball_zero_iff] at him
  have hηnorm : ‖(η : ℂ)‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp η.2)
    (le_of_not_gt fun h => hηnot (mem_ball_zero_iff.mpr h))
  have hηne : (η : ℂ) ≠ 0 := norm_ne_zero_iff.mp (by rw [hηnorm]; norm_num)
  have hrot (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : (η : ℂ) * z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff] at hz ⊢
    simpa only [norm_mul, hηnorm, one_mul] using hz
  let G₁ : ℂ → ℂ := fun z => G₀ ((η : ℂ) * z)
  have hG₁ : DifferentiableOn ℂ G₁ (ball (0 : ℂ) 1) := by
    apply hG₀.comp (by fun_prop)
    intro z hz
    exact hrot z hz
  have hG₁inj : InjOn G₁ (ball (0 : ℂ) 1) := by
    intro z hz w hw heq
    apply mul_left_cancel₀ hηne
    exact hG₀inj (hrot z hz) (hrot w hw) heq
  have hG₁image : G₁ '' ball (0 : ℂ) 1 = upperGraphDomain h := by
    rw [← hG₀image]
    apply Subset.antisymm
    · rintro w ⟨z, hz, rfl⟩
      exact ⟨(η : ℂ) * z, hrot z hz, rfl⟩
    · rintro w ⟨z, hz, rfl⟩
      have hzinv : (η : ℂ)⁻¹ * z ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff] at hz ⊢
        simpa only [norm_mul, norm_inv, hηnorm, inv_one, one_mul] using hz
      refine ⟨(η : ℂ)⁻¹ * z, hzinv, ?_⟩
      change G₀ ((η : ℂ) * ((η : ℂ)⁻¹ * z)) = G₀ z
      simp [← mul_assoc, hηne]
  have hG₁zero : G₁ 0 = p := by simpa [G₁] using hG₀zero
  let R := rotationClosedDiskHomeomorph (η : ℂ) hηnorm
  let e := R.trans e₀
  have hRone : R ⟨1, by simp⟩ = η := by
    apply Subtype.ext
    simp [R, rotationClosedDiskHomeomorph]
  refine ⟨G₁, hG₁, hG₁inj, hG₁image, hG₁zero, e, ?_, ?_⟩
  · intro z hz
    have hRz : (R z : ℂ) ∈ ball (0 : ℂ) 1 := hrot z hz
    calc
      (e z : ℂ) = diskExtension F₀ (R z) := he₀ (R z)
      _ = F₀ (R z) := diskExtension_eqOn F₀ hF₀ hRz
      _ = halfPlaneToCayley (G₁ z) := rfl
  · change (e₀ (R ⟨1, by simp⟩) : ℂ) = 1
    rw [hRone]
    exact heη

end ThreeOmittedValues
