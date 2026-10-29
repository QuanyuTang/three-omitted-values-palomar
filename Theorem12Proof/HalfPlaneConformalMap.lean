module

public import Theorem12Proof.FareyCompactEmbedding
public import Theorem12Proof.DiskNormalization
import Mathlib.Tactic

/-!
# Passing a normalized disk map to the upper half-plane

The Cayley transform sends `i` to the disk center, giving the prescribed
interior normalization used by the paper.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem halfPlaneToCayley_image_upper :
    halfPlaneToCayley '' {z : ℂ | 0 < z.im} = ball (0 : ℂ) 1 := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact halfPlaneToCayley_mem_ball hz
  · intro hw
    exact ⟨cayleyToHalfPlane w, cayleyToHalfPlane_im_pos hw,
      halfPlaneToCayley_cayleyToHalfPlane hw⟩

theorem disk_map_to_upper_halfPlane {Ω : Set ℂ} {G : ℂ → ℂ} {p : ℂ}
    (hG : DifferentiableOn ℂ G (ball (0 : ℂ) 1))
    (hGinj : InjOn G (ball (0 : ℂ) 1))
    (hGimage : G '' ball (0 : ℂ) 1 = Ω) (hGzero : G 0 = p) :
    ∃ Φ : ℂ → ℂ,
      DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im} ∧
      InjOn Φ {z : ℂ | 0 < z.im} ∧ Φ '' {z : ℂ | 0 < z.im} = Ω ∧
      Φ Complex.I = p ∧ Φ = G ∘ halfPlaneToCayley := by
  let Φ := G ∘ halfPlaneToCayley
  have hmaps : MapsTo halfPlaneToCayley {z : ℂ | 0 < z.im} (ball (0 : ℂ) 1) := by
    intro z hz
    exact halfPlaneToCayley_mem_ball hz
  have hc : DifferentiableOn ℂ halfPlaneToCayley {z : ℂ | 0 < z.im} := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hden : z + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos hz
    unfold halfPlaneToCayley
    fun_prop (disch := exact hden)
  have hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im} := hG.comp hc hmaps
  have hΦinj : InjOn Φ {z : ℂ | 0 < z.im} := by
    intro z hz w hw heq
    apply halfPlaneToCayley_injective_of_denominators
      (add_I_ne_zero_of_im_pos hz) (add_I_ne_zero_of_im_pos hw)
    exact hGinj (hmaps hz) (hmaps hw) heq
  have himage : Φ '' {z : ℂ | 0 < z.im} = Ω := by
    rw [Set.image_comp, halfPlaneToCayley_image_upper, hGimage]
  have hcenter : Φ Complex.I = p := by simpa [Φ, halfPlaneToCayley] using hGzero
  exact ⟨Φ, hΦ, hΦinj, himage, hcenter, rfl⟩

end ThreeOmittedValues
