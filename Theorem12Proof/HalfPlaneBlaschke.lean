module

public import Theorem12Proof.JensenDiskZeros
public import Theorem12Proof.HalfPlaneWeight
import Mathlib.Tactic

/-!
# The Blaschke condition for half-plane zeros

This derives the upper-half-plane zero-set theorem from Jensen's formula in
the disk and the explicit Cayley transform. It applies to an arbitrary
injective family of zeros of a nonzero bounded analytic function.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem summable_halfPlane_zero_weights {ι : Type*} (a : ι → ℂ)
    (ha : Function.Injective a) {f : ℂ → ℂ} {C : ℝ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im})
    (hbound : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ C)
    (hnontrivial : ∃ p : ℂ, 0 < p.im ∧ f p ≠ 0)
    (hzeros : ∀ i, 0 < (a i).im ∧ f (a i) = 0) :
    Summable (fun i => blaschkeWeight (a i)) := by
  let b : ι → ℂ := fun i => halfPlaneToCayley (a i)
  have hbmem (i : ι) : b i ∈ ball (0 : ℂ) 1 := halfPlaneToCayley_mem_ball (hzeros i).1
  have hbinj : Function.Injective b := by
    intro i j hij
    apply ha
    have heq := congrArg cayleyToHalfPlane hij
    simpa only [b, cayleyToHalfPlane_halfPlaneToCayley (hzeros i).1,
      cayleyToHalfPlane_halfPlaneToCayley (hzeros j).1] using heq
  have hcayleydiff : DifferentiableOn ℂ cayleyToHalfPlane (ball 0 1) := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    unfold cayleyToHalfPlane
    fun_prop (disch := exact one_sub_ne_zero_of_mem_ball hz)
  have hmaps : MapsTo cayleyToHalfPlane (ball (0 : ℂ) 1) {z : ℂ | 0 < z.im} := by
    intro z hz
    exact cayleyToHalfPlane_im_pos hz
  let g : ℂ → ℂ := fun z => f (cayleyToHalfPlane z)
  have hg : AnalyticOnNhd ℂ g (ball 0 1) :=
    hf.comp (hcayleydiff.analyticOnNhd isOpen_ball) hmaps
  have hgbound : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ C := by
    intro z hz
    exact hbound _ (hmaps hz)
  have hgnontrivial : ∃ p ∈ ball (0 : ℂ) 1, g p ≠ 0 := by
    obtain ⟨p, hp, hpval⟩ := hnontrivial
    refine ⟨halfPlaneToCayley p, halfPlaneToCayley_mem_ball hp, ?_⟩
    simpa only [g, cayleyToHalfPlane_halfPlaneToCayley hp] using hpval
  have hbzero : ∀ i, b i ∈ ball (0 : ℂ) 1 ∧ g (b i) = 0 := by
    intro i
    refine ⟨hbmem i, ?_⟩
    simpa only [g, b, cayleyToHalfPlane_halfPlaneToCayley (hzeros i).1] using (hzeros i).2
  have hsum : Summable (fun i => 1 - ‖b i‖) :=
    summable_zero_weights_of_bounded_analytic b hbinj hg hgbound hgnontrivial hbzero
  apply hsum.of_nonneg_of_le
  · intro i
    unfold blaschkeWeight
    positivity
  · intro i
    exact halfPlane_blaschkeWeight_le_cayley (hzeros i).1

end ThreeOmittedValues
