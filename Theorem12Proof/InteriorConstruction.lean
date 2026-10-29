module

public import Theorem12Proof.FareyOrbitDivergence
public import Theorem12Proof.NoWanderingDomains.Hyperbolic.Gamma2FundamentalDomain.Surjectivity
import Mathlib.Tactic

/-!
# The upper-half-plane part of the construction

There is a single normalized Farey map such that every value other than
`0` and `1` has an injective, non-Blaschke family of preimages for the
composite with the modular lambda function. The composite omits `0` and `1`
in the upper half-plane. The global meromorphic extension is established
in `FareyGlobalExtension`.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set NoWanderingDomains
open scoped ModularForm Manifold MatrixGroups

namespace ThreeOmittedValues

theorem exists_farey_map_with_all_divergent_interior_fibres :
    ∃ (levels : ℤ → ℕ) (Φ : ℂ → ℂ),
      (∀ n, 1 ≤ levels n) ∧
      (∀ x, 0 ≤ pastedFareyHeight levels x ∧ pastedFareyHeight levels x < gaussianBeta x) ∧
      (∀ n : ℤ, pastedFareyHeight levels (n : ℝ) = 0 ∧
        pastedFareyHeight levels ((n : ℝ) + 1 / 2) = 0) ∧
      globalFareyArcs levels = Set.range (graphMap (pastedFareyHeight levels)) ∧
      upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im} ∧ InjOn Φ {z : ℂ | 0 < z.im} ∧
      Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels) ∧
      Φ Complex.I = gaussianPerturbation Complex.I ∧
      DifferentiableOn ℂ (fun z => modularLambdaH (Φ z)) {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → modularLambdaH (Φ z) ≠ 0 ∧ modularLambdaH (Φ z) ≠ 1) ∧
      (∀ a : ℂ, a ≠ 0 → a ≠ 1 →
        ∃ (N : ℕ) (p : OrbitIndexFrom N → ℂ),
          Function.Injective p ∧
          (∀ i, 0 < (p i).im ∧ modularLambdaH (Φ (p i)) = a) ∧
          ¬ Summable (fun i => blaschkeWeight (p i))) ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ
          closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)),
        (∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
          (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z))) ∧
        (e ⟨1, by simp⟩ : ℂ) = 1 := by
  obtain ⟨levels, Φ, G, hlevels, hbelow, hvertices, _hproper, harcs, hsubset, hupper,
    hΦ, hΦinj, hΦimage, hΦcenter, _hG, hGmaps, _hGΦ, hΦG, hweight, e, he, he1⟩ :=
    exists_gaussian_farey_comparison
  have hΦmaps : MapsTo Φ {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} := by
    intro z hz
    apply hupper
    rw [← hΦimage]
    exact ⟨z, hz, rfl⟩
  have hf : DifferentiableOn ℂ (fun z => modularLambdaH (Φ z)) {z : ℂ | 0 < z.im} :=
    modularLambdaH_differentiableOn.comp hΦ hΦmaps
  have homits : ∀ z : ℂ, 0 < z.im → modularLambdaH (Φ z) ≠ 0 ∧ modularLambdaH (Φ z) ≠ 1 := by
    intro z hz
    exact ⟨modularLambdaH_ne_zero (hΦmaps hz), modularLambdaH_ne_one (hΦmaps hz)⟩
  have hall (a : ℂ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
      ∃ (N : ℕ) (p : OrbitIndexFrom N → ℂ), Function.Injective p ∧
        (∀ i, 0 < (p i).im ∧ modularLambdaH (Φ (p i)) = a) ∧
        ¬ Summable (fun i => blaschkeWeight (p i)) := by
    have ha : a ∈ modularLambdaH '' {z : ℂ | 0 < z.im} := by
      rw [modularLambdaH_image]
      exact ⟨ha0, ha1⟩
    obtain ⟨z, hz, hza⟩ := ha
    let τ : UpperHalfPlane := ⟨z, hz⟩
    obtain ⟨N, p, hp_inj, hp_fibre, hp_div⟩ :=
      farey_comparison_has_divergent_orbit hsubset hGmaps hΦG hweight τ
    refine ⟨N, p, hp_inj, ?_, hp_div⟩
    intro i
    have hi := hp_fibre i
    exact ⟨hi.1, hi.2.trans hza⟩
  exact ⟨levels, Φ, hlevels, hbelow, hvertices, harcs, hupper, hΦ, hΦinj, hΦimage,
    hΦcenter, hf, homits, hall, e, he, he1⟩

end ThreeOmittedValues
