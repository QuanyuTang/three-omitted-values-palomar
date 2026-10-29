module

public import Theorem12Proof.NormalizedFareyMap
public import Theorem12Proof.CayleyPartialHomeomorph
import Mathlib.Tactic

/-!
# From the closed disk extension to the closed upper half-plane

A normalized disk homeomorphism gives a continuous finite extension of the
conformal map to every finite real boundary point. The compactified point at
infinity is excluded by the normalization and injectivity.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem add_I_ne_zero_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : z + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

theorem halfPlaneToCayley_mem_closedBall {z : ℂ} (hz : 0 ≤ z.im) :
    halfPlaneToCayley z ∈ closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall, dist_zero_right]
  unfold halfPlaneToCayley
  rw [norm_div, div_le_one (norm_pos_iff.mpr (add_I_ne_zero_of_im_nonneg hz))]
  have hs : ‖z - Complex.I‖ ^ 2 ≤ ‖z + Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im]
    nlinarith
  nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]

noncomputable def closedHalfPlaneCayley (z : {z : ℂ // 0 ≤ z.im}) : closedBall (0 : ℂ) 1 :=
  ⟨halfPlaneToCayley z, halfPlaneToCayley_mem_closedBall z.2⟩

theorem closedHalfPlaneCayley_continuous : Continuous closedHalfPlaneCayley := by
  apply Continuous.subtype_mk
  have hden : ∀ z : {z : ℂ // 0 ≤ z.im}, (z : ℂ) + Complex.I ≠ 0 :=
    fun z => add_I_ne_zero_of_im_nonneg z.2
  unfold halfPlaneToCayley
  exact (continuous_subtype_val.sub continuous_const).div
    (continuous_subtype_val.add continuous_const) hden

theorem closedHalfPlaneCayley_ne_one (z : {z : ℂ // 0 ≤ z.im}) :
    (closedHalfPlaneCayley z : ℂ) ≠ 1 :=
  halfPlaneToCayley_ne_one_of_denominator (add_I_ne_zero_of_im_nonneg z.2)

theorem closedDiskBoundaryImage_ne_one {Ω : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ closure (halfPlaneToCayley '' Ω))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (z : {z : ℂ // 0 ≤ z.im}) :
    (e (closedHalfPlaneCayley z) : ℂ) ≠ 1 := by
  intro h
  have heq : e (closedHalfPlaneCayley z) = e ⟨1, by simp⟩ :=
    Subtype.ext (h.trans he1.symm)
  have hq := congrArg Subtype.val (e.injective heq)
  exact closedHalfPlaneCayley_ne_one z hq

noncomputable def closedHalfPlaneMap {Ω : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ closure (halfPlaneToCayley '' Ω))
    (z : {z : ℂ // 0 ≤ z.im}) : ℂ :=
  cayleyToHalfPlane (e (closedHalfPlaneCayley z))

theorem closedHalfPlaneMap_continuous {Ω : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ closure (halfPlaneToCayley '' Ω))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) : Continuous (closedHalfPlaneMap e) := by
  have hc : Continuous (fun z : {z : ℂ // 0 ≤ z.im} =>
      (e (closedHalfPlaneCayley z) : ℂ)) :=
    continuous_subtype_val.comp (e.continuous.comp closedHalfPlaneCayley_continuous)
  unfold closedHalfPlaneMap cayleyToHalfPlane
  exact (continuous_const.mul (continuous_const.add hc)).div (continuous_const.sub hc)
    (fun z => sub_ne_zero.mpr (Ne.symm (closedDiskBoundaryImage_ne_one e he1 z)))

noncomputable def halfPlaneContinuousExtension {Ω : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ closure (halfPlaneToCayley '' Ω)) (z : ℂ) : ℂ :=
  if hz : 0 ≤ z.im then closedHalfPlaneMap e ⟨z, hz⟩ else 0

theorem halfPlaneContinuousExtension_continuousOn {Ω : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ closure (halfPlaneToCayley '' Ω))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) :
    ContinuousOn (halfPlaneContinuousExtension e) {z : ℂ | 0 ≤ z.im} := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun z : {z : ℂ // 0 ≤ z.im} => halfPlaneContinuousExtension e z)
  have heq : (fun z : {z : ℂ // 0 ≤ z.im} => halfPlaneContinuousExtension e z) =
      closedHalfPlaneMap e := by
    funext z
    simp [halfPlaneContinuousExtension, z.2]
  rw [heq]
  exact closedHalfPlaneMap_continuous e he1

theorem halfPlaneContinuousExtension_interior {Ω : Set ℂ} {Φ : ℂ → ℂ}
    (hupper : Ω ⊆ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = Ω)
    (e : closedBall (0 : ℂ) 1 ≃ₜ closure (halfPlaneToCayley '' Ω))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    {z : ℂ} (hz : 0 < z.im) : halfPlaneContinuousExtension e z = Φ z := by
  have hΦz : 0 < (Φ z).im := hupper (by rw [← hΦimage]; exact ⟨z, hz, rfl⟩)
  rw [halfPlaneContinuousExtension, dif_pos hz.le]
  unfold closedHalfPlaneMap
  rw [he (closedHalfPlaneCayley ⟨z, hz.le⟩) (halfPlaneToCayley_mem_ball hz)]
  change cayleyToHalfPlane (halfPlaneToCayley (Φ (cayleyToHalfPlane (halfPlaneToCayley z)))) = Φ z
  rw [cayleyToHalfPlane_halfPlaneToCayley hz, cayleyToHalfPlane_halfPlaneToCayley hΦz]

end ThreeOmittedValues
