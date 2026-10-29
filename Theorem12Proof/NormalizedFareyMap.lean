module

public import Theorem12Proof.FareyNormalization
public import Theorem12Proof.HalfPlaneConformalMap
import Mathlib.Tactic

/-!
# The normalized upper-half-plane map for a Farey domain

The closed-disk homeomorphism supplies the boundary normalization at
infinity in Cayley coordinates. The comparison domain and modular
meromorphic continuation are not constructed in this file.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem exists_normalized_upper_farey_map (levels : ℤ → ℕ) (G : ℂ → ℂ) (p : ℂ)
    (hG : DifferentiableOn ℂ G (ball (0 : ℂ) 1))
    (hGinj : InjOn G (ball (0 : ℂ) 1))
    (hGimage : G '' ball (0 : ℂ) 1 = upperGraphDomain (pastedFareyHeight levels))
    (hp : p ∈ upperGraphDomain (pastedFareyHeight levels)) :
    ∃ Φ : ℂ → ℂ,
      DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im} ∧
      InjOn Φ {z : ℂ | 0 < z.im} ∧
      Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels) ∧
      Φ Complex.I = p ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ
          closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)),
        (∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
          (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z))) ∧
        (e ⟨1, by simp⟩ : ℂ) = 1 := by
  obtain ⟨G₁, hG₁, hG₁inj, hG₁image, hG₁zero, e, he, he1⟩ :=
    exists_farey_map_normalized_at_point_and_infinity levels G p hG hGinj hGimage hp
  obtain ⟨Φ, hΦ, hΦinj, hΦimage, hΦcenter, hΦeq⟩ :=
    disk_map_to_upper_halfPlane hG₁ hG₁inj hG₁image hG₁zero
  refine ⟨Φ, hΦ, hΦinj, hΦimage, hΦcenter, e, ?_, he1⟩
  intro z hz
  rw [hΦeq, Function.comp_apply, halfPlaneToCayley_cayleyToHalfPlane hz]
  exact he z hz

theorem exists_farey_domain_with_normalized_map (β : ℝ → ℝ)
    (hβcont : Continuous β) (hβpos : ∀ x, 0 < β x) (p : ℂ)
    (hp : p ∈ upperGraphDomain β) :
    ∃ (levels : ℤ → ℕ) (Φ : ℂ → ℂ),
      (∀ n, 1 ≤ levels n) ∧
      (∀ x, 0 ≤ pastedFareyHeight levels x ∧ pastedFareyHeight levels x < β x) ∧
      (∀ n : ℤ, pastedFareyHeight levels (n : ℝ) = 0 ∧
        pastedFareyHeight levels ((n : ℝ) + 1 / 2) = 0) ∧
      IsProperMap (graphMap (pastedFareyHeight levels)) ∧
      globalFareyArcs levels = Set.range (graphMap (pastedFareyHeight levels)) ∧
      upperGraphDomain β ⊆ upperGraphDomain (pastedFareyHeight levels) ∧
      upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im} ∧
      InjOn Φ {z : ℂ | 0 < z.im} ∧
      Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels) ∧
      Φ Complex.I = p ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ
          closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)),
        (∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
          (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z))) ∧
        (e ⟨1, by simp⟩ : ℂ) = 1 := by
  obtain ⟨levels, G, hlevels, hbelow, hvertices, hproper, harcs, _hopen, _hsc,
    hsubset, hupper, hG, hGinj, hGimage⟩ := exists_farey_domain_with_interior_map β hβcont hβpos
  obtain ⟨Φ, hΦ, hΦinj, hΦimage, hΦcenter, e, he, he1⟩ :=
    exists_normalized_upper_farey_map levels G p hG hGinj hGimage (hsubset hp)
  exact ⟨levels, Φ, hlevels, hbelow, hvertices, hproper, harcs, hsubset, hupper,
    hΦ, hΦinj, hΦimage, hΦcenter, e, he, he1⟩

end ThreeOmittedValues
