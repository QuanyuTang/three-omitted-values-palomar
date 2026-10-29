module

public import Theorem12Proof.FareyGraphVariation
public import Theorem12Proof.NoWanderingDomains.Hyperbolic.DiskModel.DiskMetric
import Mathlib.Tactic

/-!
# Compactification contracts the tails of the Farey graph

On the graph over `[n,n+1]`, the Cayley compactification is Lipschitz with
constant at most `6/(1+n²)`. Combining this with the local graph-length
bound gives a summable candidate bound for the compactified boundary.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains
open scoped ENNReal NNReal

namespace ThreeOmittedValues

noncomputable def compactUnitLipschitz (n : ℤ) : ℝ≥0 :=
  ⟨6 / (1 + (n : ℝ) ^ 2), by positivity⟩

theorem graph_denominator_ne {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x) (x : ℝ) :
    graphMap h x + Complex.I ≠ 0 := by
  intro heq
  have him := congrArg Complex.im heq
  simp only [Complex.add_im, graphMap_im, Complex.I_im, Complex.zero_im] at him
  linarith [hh x]

theorem graph_denominator_sq_lower {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x)
    (n : ℤ) {x : ℝ} (hx : x ∈ Icc (n : ℝ) ((n : ℝ) + 1)) :
    1 + (n : ℝ) ^ 2 ≤ 3 * ‖graphMap h x + Complex.I‖ ^ 2 := by
  have hdiff : ((n : ℝ) - x) ^ 2 ≤ 1 := by
    have h := mul_nonneg (show 0 ≤ 1 + ((n : ℝ) - x) by linarith [hx.2])
      (show 0 ≤ 1 - ((n : ℝ) - x) by linarith [hx.1])
    nlinarith
  have hnsq : (n : ℝ) ^ 2 ≤ 2 * x ^ 2 + 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2 * x)]
  have hnorm : ‖graphMap h x + Complex.I‖ ^ 2 = x ^ 2 + (h x + 1) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      graphMap_re, graphMap_im, Complex.I_re, Complex.I_im, add_zero]
    ring
  rw [hnorm]
  nlinarith [hh x, sq_nonneg (h x), sq_nonneg x]

theorem compact_graph_distance_le {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x)
    (n : ℤ) {x y : ℝ}
    (hx : x ∈ Icc (n : ℝ) ((n : ℝ) + 1))
    (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 1)) :
    dist (halfPlaneToCayley (graphMap h x)) (halfPlaneToCayley (graphMap h y)) ≤
      (6 / (1 + (n : ℝ) ^ 2)) * dist (graphMap h x) (graphMap h y) := by
  let zx := graphMap h x
  let zy := graphMap h y
  have hxne : zx + Complex.I ≠ 0 := graph_denominator_ne hh x
  have hyne : zy + Complex.I ≠ 0 := graph_denominator_ne hh y
  have hdiff : halfPlaneToCayley zx - halfPlaneToCayley zy =
      2 * Complex.I * (zx - zy) / ((zx + Complex.I) * (zy + Complex.I)) := by
    unfold halfPlaneToCayley
    field_simp
    ring
  have hdist : dist (halfPlaneToCayley zx) (halfPlaneToCayley zy) =
      2 * dist zx zy / (‖zx + Complex.I‖ * ‖zy + Complex.I‖) := by
    calc
      dist (halfPlaneToCayley zx) (halfPlaneToCayley zy) =
          ‖2 * Complex.I * (zx - zy) / ((zx + Complex.I) * (zy + Complex.I))‖ := by
        rw [dist_eq_norm, hdiff]
      _ = 2 * dist zx zy / (‖zx + Complex.I‖ * ‖zy + Complex.I‖) := by
        simp [norm_div, norm_mul, dist_eq_norm]
  let c : ℝ := (1 + (n : ℝ) ^ 2) / 3
  have hc : 0 < c := by dsimp [c]; positivity
  have hxsq : c ≤ ‖zx + Complex.I‖ ^ 2 := by
    dsimp [c, zx]
    have hhx := graph_denominator_sq_lower hh n hx
    linarith
  have hysq : c ≤ ‖zy + Complex.I‖ ^ 2 := by
    dsimp [c, zy]
    have hhy := graph_denominator_sq_lower hh n hy
    linarith
  have hprodSq : c ^ 2 ≤ (‖zx + Complex.I‖ * ‖zy + Complex.I‖) ^ 2 := by
    have hprod := mul_le_mul hxsq hysq hc.le (sq_nonneg _)
    nlinarith
  have hprod : c ≤ ‖zx + Complex.I‖ * ‖zy + Complex.I‖ := by
    have hnon : 0 ≤ ‖zx + Complex.I‖ * ‖zy + Complex.I‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith
  have hPpos : 0 < ‖zx + Complex.I‖ * ‖zy + Complex.I‖ := by positivity
  have hratio : 2 / (‖zx + Complex.I‖ * ‖zy + Complex.I‖) ≤
      6 / (1 + (n : ℝ) ^ 2) := by
    apply (div_le_div_iff₀ hPpos (by positivity : 0 < 1 + (n : ℝ) ^ 2)).2
    dsimp [c] at hprod
    nlinarith
  calc
    _ = (2 / (‖zx + Complex.I‖ * ‖zy + Complex.I‖)) * dist zx zy := by
      rw [hdist]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (dist_nonneg)

theorem compactifier_lipschitz_graph_unit {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x) (n : ℤ) :
    LipschitzOnWith (compactUnitLipschitz n) halfPlaneToCayley
      (graphMap h '' Icc (n : ℝ) ((n : ℝ) + 1)) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact compact_graph_distance_le hh n hx hy

theorem compactFareyGraph_variation_unit (levels : ℤ → ℕ) (n : ℤ) :
    eVariationOn (halfPlaneToCayley ∘ graphMap (pastedFareyHeight levels))
      (Icc (n : ℝ) ((n : ℝ) + 1)) ≤ (compactUnitLipschitz n : ℝ≥0∞) * 2 := by
  have hh : ∀ x, 0 ≤ pastedFareyHeight levels x := pastedFareyHeight_nonneg levels
  have hLip := compactifier_lipschitz_graph_unit hh n
  have hmaps : MapsTo (graphMap (pastedFareyHeight levels))
      (Icc (n : ℝ) ((n : ℝ) + 1))
      (graphMap (pastedFareyHeight levels) '' Icc (n : ℝ) ((n : ℝ) + 1)) :=
    mapsTo_image _ _
  calc
    _ ≤ (compactUnitLipschitz n : ℝ≥0∞) *
        eVariationOn (graphMap (pastedFareyHeight levels))
          (Icc (n : ℝ) ((n : ℝ) + 1)) := hLip.comp_eVariationOn_le hmaps
    _ ≤ (compactUnitLipschitz n : ℝ≥0∞) * 2 :=
      by gcongr; exact pastedFareyGraph_variation_unit levels n

end ThreeOmittedValues
