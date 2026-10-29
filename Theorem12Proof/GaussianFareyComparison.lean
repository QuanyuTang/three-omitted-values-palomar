module

public import Theorem12Proof.GaussianComparisonDomain
public import Theorem12Proof.ComparisonDomainSchwarz
public import Theorem12Proof.NormalizedFareyMap
import Mathlib.Tactic

/-!
# A normalized Farey map with quantitative Gaussian comparison

This combines the actual Gaussian epigraph, the unconditional Farey-domain
construction and closed-disk extension, and Schwarz's lemma. The resulting
weight estimate is uniform for points above twice the comparison height.
The meromorphic continuation of modular lambda is constructed in later modules.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem exists_gaussian_farey_comparison :
    ∃ (levels : ℤ → ℕ) (Φ G : ℂ → ℂ),
      (∀ n, 1 ≤ levels n) ∧
      (∀ x, 0 ≤ pastedFareyHeight levels x ∧ pastedFareyHeight levels x < gaussianBeta x) ∧
      (∀ n : ℤ, pastedFareyHeight levels (n : ℝ) = 0 ∧
        pastedFareyHeight levels ((n : ℝ) + 1 / 2) = 0) ∧
      IsProperMap (graphMap (pastedFareyHeight levels)) ∧
      globalFareyArcs levels = Set.range (graphMap (pastedFareyHeight levels)) ∧
      upperGraphDomain gaussianBeta ⊆ upperGraphDomain (pastedFareyHeight levels) ∧
      upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im} ∧
      InjOn Φ {z : ℂ | 0 < z.im} ∧
      Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels) ∧
      Φ Complex.I = gaussianPerturbation Complex.I ∧
      DifferentiableOn ℂ G (upperGraphDomain (pastedFareyHeight levels)) ∧
      MapsTo G (upperGraphDomain (pastedFareyHeight levels)) {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → G (Φ z) = z) ∧
      (∀ w ∈ upperGraphDomain (pastedFareyHeight levels), Φ (G w) = w) ∧
      (∀ w : ℂ, w.im ≤ 1 → gaussianBeta w.re ≤ w.im / 2 →
        w.im / (128 * (1 + w.re ^ 2)) ≤ blaschkeWeight (G w)) ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ
          closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)),
        (∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
          (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z))) ∧
        (e ⟨1, by simp⟩ : ℂ) = 1 := by
  have hp : gaussianPerturbation Complex.I ∈ upperGraphDomain gaussianBeta :=
    gaussianPerturbation_image_above_graph (by simp)
  obtain ⟨levels, Φ, hlevels, hbelow, hvertices, hproper, harcs, hsubset, hupper,
    hΦ, hΦinj, hΦimage, hΦcenter, e, he, he1⟩ :=
    exists_farey_domain_with_normalized_map gaussianBeta gaussianBeta_continuous gaussianBeta_pos
      (gaussianPerturbation Complex.I) hp
  have hψmaps : MapsTo gaussianPerturbation {z : ℂ | 0 < z.im}
      (Φ '' {z : ℂ | 0 < z.im}) := by
    intro z hz
    rw [hΦimage]
    apply hsubset
    exact gaussianPerturbation_image_above_graph hz
  obtain ⟨G, hG, hGmaps, hGΦ, hΦG, hGweight⟩ :=
    normalized_comparison_domain_weight hΦ hΦinj
      gaussianPerturbation_differentiable.differentiableOn hψmaps hΦcenter.symm
  have hG' : DifferentiableOn ℂ G (upperGraphDomain (pastedFareyHeight levels)) := by
    simpa only [hΦimage] using hG
  have hGmaps' : MapsTo G (upperGraphDomain (pastedFareyHeight levels)) {z : ℂ | 0 < z.im} := by
    simpa only [hΦimage] using hGmaps
  have hΦG' : ∀ w ∈ upperGraphDomain (pastedFareyHeight levels), Φ (G w) = w := by
    simpa only [hΦimage] using hΦG
  have hweight (w : ℂ) (hw1 : w.im ≤ 1) (hwβ : gaussianBeta w.re ≤ w.im / 2) :
      w.im / (128 * (1 + w.re ^ 2)) ≤ blaschkeWeight (G w) := by
    obtain ⟨z, hz, heq, hlow⟩ := gaussian_inverse_weight hw1 hwβ
    have hcomp := hGweight z hz
    rw [heq] at hcomp
    have hid : w.im / (32 * (1 + w.re ^ 2)) =
        4 * (w.im / (128 * (1 + w.re ^ 2))) := by
      field_simp
      ring
    rw [hid] at hlow
    linarith
  exact ⟨levels, Φ, G, hlevels, hbelow, hvertices, hproper, harcs, hsubset, hupper,
    hΦ, hΦinj, hΦimage, hΦcenter, hG', hGmaps', hGΦ, hΦG', hweight, e, he, he1⟩

end ThreeOmittedValues
