module

public import Theorem12Proof.OrbitGaussianTail
public import Theorem12Proof.GaussianFareyComparison
import Mathlib.Tactic

/-!
# Divergent modular fibres for the normalized Farey map

These are interior results. Extending the composite meromorphically across
the Farey boundary and identifying its three exceptional fibres are separate
remaining obligations.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set NoWanderingDomains
open scoped ModularForm Manifold MatrixGroups

namespace ThreeOmittedValues

theorem farey_comparison_has_divergent_orbit {levels : ℤ → ℕ} {Φ G : ℂ → ℂ}
    (hsubset : upperGraphDomain gaussianBeta ⊆ upperGraphDomain (pastedFareyHeight levels))
    (hGmaps : MapsTo G (upperGraphDomain (pastedFareyHeight levels)) {z : ℂ | 0 < z.im})
    (hΦG : ∀ w ∈ upperGraphDomain (pastedFareyHeight levels), Φ (G w) = w)
    (hweight : ∀ w : ℂ, w.im ≤ 1 → gaussianBeta w.re ≤ w.im / 2 →
      w.im / (128 * (1 + w.re ^ 2)) ≤ blaschkeWeight (G w))
    (τ : UpperHalfPlane) :
    ∃ (N : ℕ) (p : OrbitIndexFrom N → ℂ),
      Function.Injective p ∧
      (∀ i, 0 < (p i).im ∧
        NoWanderingDomains.modularLambdaH (Φ (p i)) = NoWanderingDomains.modularLambdaH (τ : ℂ)) ∧
      ¬ Summable (fun i => blaschkeWeight (p i)) := by
  obtain ⟨N, hN, htail⟩ := exists_shifted_orbit_gaussian_tail τ
  let w : OrbitIndexFrom N → ℂ := shiftedOrbitPoint N hN (logarithmicOrbitShift τ) τ
  let p : OrbitIndexFrom N → ℂ := fun i => G (w i)
  have hwpos (i : OrbitIndexFrom N) : 0 < (w i).im := by
    have ht := htail i
    have hb := gaussianBeta_pos (w i).re
    dsimp [w] at *
    linarith
  have hwΩ (i : OrbitIndexFrom N) : w i ∈ upperGraphDomain (pastedFareyHeight levels) := by
    apply hsubset
    change gaussianBeta (w i).re < (w i).im
    have ht := htail i
    have hp := hwpos i
    dsimp [w] at *
    linarith
  have hp_inj : Function.Injective p := by
    intro i j hij
    apply shiftedOrbitPoint_injective N hN (logarithmicOrbitShift τ) τ
    have h := congrArg Φ hij
    dsimp [p] at h
    rw [hΦG (w i) (hwΩ i), hΦG (w j) (hwΩ j)] at h
    exact h
  have hp_fibre (i : OrbitIndexFrom N) : 0 < (p i).im ∧
      modularLambdaH (Φ (p i)) = modularLambdaH (τ : ℂ) := by
    refine ⟨hGmaps (hwΩ i), ?_⟩
    dsimp [p]
    rw [hΦG (w i) (hwΩ i)]
    exact shiftedOrbitPoint_lambda N hN (logarithmicOrbitShift τ) τ i
  let A := orbitHeightLower τ
  let D := orbitLogConstant τ
  let c : ℝ := A / (128 * D)
  have hA : 0 < A := orbitHeightLower_pos τ
  have hD : 0 < D := orbitLogConstant_pos τ
  have hc : 0 < c := by dsimp [c]; positivity
  have hp_bound (i : OrbitIndexFrom N) :
      c / ((i.1.1 : ℝ) ^ 2 * Real.log (i.1.1 : ℝ)) ≤ blaschkeWeight (p i) := by
    let m : ℝ := i.1.1
    let L : ℝ := Real.log m
    let x : ℝ := (w i).re
    let y : ℝ := (w i).im
    have ht := htail i
    have hy : 0 < y := hwpos i
    have hm : 0 < m := by
      dsimp [m]
      have := i.1.2
      exact_mod_cast (show 0 < i.1.1 by omega)
    have hm2 : 0 < m ^ 2 := by positivity
    have hden : 1 + x ^ 2 ≤ D * L := ht.2.2.1
    have hheight : A / m ^ 2 ≤ y := ht.2.2.2
    have hL : 0 < L := by nlinarith [sq_nonneg x]
    have hdenpos : 0 < 128 * (1 + x ^ 2) := by positivity
    have hgeom : y / (128 * (1 + x ^ 2)) ≤ blaschkeWeight (p i) :=
      hweight (w i) ht.1 ht.2.1
    have hid : c / (m ^ 2 * L) = (A / m ^ 2) / (128 * (D * L)) := by
      dsimp [c]
      field_simp
    calc
      c / (m ^ 2 * L) = (A / m ^ 2) / (128 * (D * L)) := hid
      _ ≤ y / (128 * (D * L)) :=
        div_le_div_of_nonneg_right hheight (by positivity)
      _ ≤ y / (128 * (1 + x ^ 2)) := by
        apply div_le_div_of_nonneg_left hy.le hdenpos
        nlinarith
      _ ≤ blaschkeWeight (p i) := hgeom
  have hdiv : ¬ Summable (fun i : OrbitIndexFrom N => blaschkeWeight (p i)) := by
    apply not_summable_of_orbit_tail_lower_bound N _
      (fun i => div_nonneg (abs_nonneg _) (by positivity)) hc
    intro m d
    exact hp_bound ⟨m, d⟩
  exact ⟨N, p, hp_inj, hp_fibre, hdiv⟩

end ThreeOmittedValues
