module

public import Theorem12Proof.Vendor.DirichletRiemannMapping
import Mathlib.Tactic

/-!
# Normalizing an interior disk map

Disk automorphisms move an arbitrary prescribed interior image point to
the center of the disk. Boundary normalization is a separate step.
-/

@[expose] public section

open Complex Metric Set

namespace ThreeOmittedValues

theorem exists_disk_map_normalized_at {Ω : Set ℂ} {G : ℂ → ℂ} {p : ℂ}
    (hG : DifferentiableOn ℂ G (ball (0 : ℂ) 1))
    (hGinj : InjOn G (ball (0 : ℂ) 1))
    (hGimage : G '' ball (0 : ℂ) 1 = Ω) (hp : p ∈ Ω) :
    ∃ G₀ : ℂ → ℂ, DifferentiableOn ℂ G₀ (ball (0 : ℂ) 1) ∧
      InjOn G₀ (ball (0 : ℂ) 1) ∧ G₀ '' ball (0 : ℂ) 1 = Ω ∧ G₀ 0 = p := by
  have hp' : p ∈ G '' ball (0 : ℂ) 1 := hGimage.symm ▸ hp
  obtain ⟨q, hq, hqp⟩ := hp'
  have hqnorm : ‖q‖ < 1 := by simpa only [mem_ball_zero_iff] using hq
  have hnqnorm : ‖-q‖ < 1 := by simpa using hqnorm
  have hnq : -q ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball_zero_iff] using hnqnorm
  have hmaps : MapsTo (mob (-q)) (ball (0 : ℂ) 1) (ball 0 1) := by
    intro z hz
    exact mob_mem_ball hnq hz
  let G₀ := G ∘ mob (-q)
  have hG₀ : DifferentiableOn ℂ G₀ (ball (0 : ℂ) 1) := by
    intro z hz
    have hzNorm : ‖z‖ < 1 := by simpa only [mem_ball_zero_iff] using hz
    have hm : DifferentiableAt ℂ (mob (-q)) z := differentiableAt_mob hnqnorm hzNorm
    have hGo : DifferentiableAt ℂ G (mob (-q) z) :=
      (hG _ (hmaps hz)).differentiableAt (isOpen_ball.mem_nhds (hmaps hz))
    exact (hGo.comp z hm).differentiableWithinAt
  have hG₀inj : InjOn G₀ (ball (0 : ℂ) 1) := by
    intro z hz w hw heq
    apply mob_injOn hnqnorm hz hw
    exact hGinj (hmaps hz) (hmaps hw) heq
  have hG₀image : G₀ '' ball (0 : ℂ) 1 = Ω := by
    rw [← hGimage]
    apply Subset.antisymm
    · rintro w ⟨z, hz, rfl⟩
      exact ⟨mob (-q) z, hmaps hz, rfl⟩
    · rintro w ⟨z, hz, rfl⟩
      have hzNorm : ‖z‖ < 1 := by simpa only [mem_ball_zero_iff] using hz
      refine ⟨mob q z, mob_mem_ball hq hz, ?_⟩
      change G (mob (-q) (mob q z)) = G z
      rw [mob_neg_mob hqnorm hzNorm]
  have hG₀zero : G₀ 0 = p := by simpa only [G₀, Function.comp_apply, mob_zero, neg_neg] using hqp
  exact ⟨G₀, hG₀, hG₀inj, hG₀image, hG₀zero⟩

end ThreeOmittedValues
