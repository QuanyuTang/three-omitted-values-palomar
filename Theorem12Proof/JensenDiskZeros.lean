module

public import Theorem12Proof.JensenSummability
public import Theorem12Proof.DiskMobiusWeight
import Mathlib.Tactic

/-!
# The disk Blaschke condition for zeros

A disk automorphism moves a point at which the bounded analytic function is
nonzero to the origin; the accompanying weight comparison removes the
normalization hypothesis from the Jensen argument.
-/

@[expose] public section

open Complex Metric Set

namespace ThreeOmittedValues

theorem summable_zero_weights_of_bounded_analytic {ι : Type*} (a : ι → ℂ)
    (ha : Function.Injective a) {f : ℂ → ℂ} {C : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ C)
    (hnontrivial : ∃ p ∈ ball (0 : ℂ) 1, f p ≠ 0)
    (hzeros : ∀ i, a i ∈ ball (0 : ℂ) 1 ∧ f (a i) = 0) :
    Summable (fun i => 1 - ‖a i‖) := by
  obtain ⟨p, hp, hpval⟩ := hnontrivial
  have hpNorm : ‖p‖ < 1 := by simpa only [mem_ball_zero_iff] using hp
  have hnegNorm : ‖-p‖ < 1 := by simpa using hpNorm
  have hneg : -p ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball_zero_iff] using hnegNorm
  let b : ι → ℂ := fun i => mob p (a i)
  have hbmem (i : ι) : b i ∈ ball (0 : ℂ) 1 := mob_mem_ball hp (hzeros i).1
  have hbinj : Function.Injective b := by
    intro i j hij
    apply ha
    exact mob_injOn hpNorm (hzeros i).1 (hzeros j).1 hij
  have hmobdiff : DifferentiableOn ℂ (mob (-p)) (ball 0 1) := by
    intro z hz
    exact (differentiableAt_mob hnegNorm (by simpa only [mem_ball_zero_iff] using hz)).differentiableWithinAt
  have hmaps : MapsTo (mob (-p)) (ball (0 : ℂ) 1) (ball 0 1) := by
    intro z hz
    exact mob_mem_ball hneg hz
  let g : ℂ → ℂ := fun z => f (mob (-p) z)
  have hg : AnalyticOnNhd ℂ g (ball 0 1) :=
    hf.comp (hmobdiff.analyticOnNhd isOpen_ball) hmaps
  have hg0 : g 0 ≠ 0 := by simpa [g] using hpval
  have hgbound : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ C := by
    intro z hz
    exact hbound _ (hmaps hz)
  have hbzero : ∀ i, b i ∈ ball (0 : ℂ) 1 ∧ g (b i) = 0 := by
    intro i
    refine ⟨hbmem i, ?_⟩
    change f (mob (-p) (mob p (a i))) = 0
    have hza : ‖a i‖ < 1 := by simpa only [mem_ball_zero_iff] using (hzeros i).1
    rw [mob_neg_mob hpNorm hza]
    exact (hzeros i).2
  have hsum : Summable (fun i => 1 - ‖b i‖) :=
    summable_zero_weights_of_nonzero_origin b hbinj hg hg0 hgbound hbzero
  have hc : 0 < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  let K := 8 / (1 - ‖p‖ ^ 2)
  apply (hsum.mul_left K).of_nonneg_of_le
  · intro i
    have hi : ‖a i‖ < 1 := by simpa only [mem_ball_zero_iff] using (hzeros i).1
    linarith
  · intro i
    have hi : ‖a i‖ < 1 := by simpa only [mem_ball_zero_iff] using (hzeros i).1
    have hcomp := mob_blaschke_weight_comparison hpNorm hi
    change 1 - ‖a i‖ ≤ (8 / (1 - ‖p‖ ^ 2)) * (1 - ‖mob p (a i)‖)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).2
    nlinarith

end ThreeOmittedValues
