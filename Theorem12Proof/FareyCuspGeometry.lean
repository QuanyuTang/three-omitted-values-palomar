module

public import Theorem12Proof.FareyVertexQuadratic
public import Theorem12Proof.GraphTopology
import Mathlib.Tactic

/-!
# Approaching a Farey vertex from the domain

The graph's quadratic estimate forces a Möbius cusp height to tend to
infinity whenever points in the domain approach the vertex.
-/

@[expose] public section

open Complex Metric Set Filter
open scoped Topology

namespace ThreeOmittedValues

theorem cusp_ratio_lower {C x y : ℝ} (hC : 0 ≤ C) (hy : 0 < y) (hy1 : y ≤ 1)
    (hx : |x| ≤ C * y ^ 2) :
    1 / ((1 + C ^ 2) * y) ≤ y / (x ^ 2 + y ^ 2) := by
  have hx2 : x ^ 2 ≤ (C * y ^ 2) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hx 2
    simpa only [sq_abs] using h
  have hy4 : y ^ 4 ≤ y ^ 2 := by
    have h := mul_nonneg (sq_nonneg y) (show 0 ≤ 1 - y ^ 2 by nlinarith)
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hy4 (sq_nonneg C)
  have hden : x ^ 2 + y ^ 2 ≤ (1 + C ^ 2) * y ^ 2 := by
    nlinarith [hx2, hprod]
  apply (div_le_div_iff₀ (by positivity : 0 < (1 + C ^ 2) * y)
    (by positivity : 0 < x ^ 2 + y ^ 2)).2
  nlinarith [hden]

theorem farey_vertex_ratio_closed_tendsto_atTop {α : Type*} {l : Filter α}
    (levels : ℤ → ℕ) (r : ℝ) (hr0 : pastedFareyHeight levels r = 0)
    (T : α → ℂ) (hT : Tendsto T l (𝓝 (r : ℂ)))
    (hdom : ∀ᶠ a in l, pastedFareyHeight levels (T a).re ≤ (T a).im ∧ 0 < (T a).im) :
    Tendsto (fun a => (T a).im / (((T a).re - r) ^ 2 + (T a).im ^ 2)) l atTop := by
  obtain ⟨ε, C, hε, hC, hquad⟩ := pastedFarey_vertex_quadratic levels r hr0
  have him0 : Tendsto (fun a => (T a).im) l (𝓝 0) := by
    simpa [Function.comp_def] using! Complex.continuous_im.continuousAt.tendsto.comp hT
  have hreal : Tendsto (fun a => (T a).re) l (𝓝 r) := by
    simpa [Function.comp_def] using! Complex.continuous_re.continuousAt.tendsto.comp hT
  have himpos : ∀ᶠ a in l, 0 < (T a).im := by
    filter_upwards [hdom] with a ha
    exact ha.2
  have himGT : Tendsto (fun a => (T a).im) l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨him0, himpos⟩
  have hinv : Tendsto (fun a => ((T a).im)⁻¹) l atTop :=
    tendsto_inv_nhdsGT_zero.comp himGT
  have hcpos : 0 < (1 + C ^ 2)⁻¹ := by positivity
  have hlower : Tendsto (fun a => 1 / ((1 + C ^ 2) * (T a).im)) l atTop := by
    have h := hinv.const_mul_atTop hcpos
    simpa [one_div, mul_inv_rev, mul_comm] using h
  have hnear : ∀ᶠ a in l, |(T a).re - r| < ε := by
    filter_upwards [hreal.eventually (ball_mem_nhds r hε)] with a ha
    simpa [mem_ball, Real.dist_eq] using ha
  have hy1 : ∀ᶠ a in l, (T a).im ≤ 1 := by
    filter_upwards [him0.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with a ha
    exact ha.le
  have hbound : ∀ᶠ a in l,
      1 / ((1 + C ^ 2) * (T a).im) ≤
        (T a).im / (((T a).re - r) ^ 2 + (T a).im ^ 2) := by
    filter_upwards [hdom, hnear, hy1, himpos] with a ha hclose hy_le hy_pos
    have hh0 := pastedFareyHeight_nonneg levels (T a).re
    have hh_le : pastedFareyHeight levels (T a).re ≤ (T a).im := ha.1
    have hsq : (pastedFareyHeight levels (T a).re) ^ 2 ≤ (T a).im ^ 2 :=
      pow_le_pow_left₀ hh0 hh_le 2
    have hx := (hquad (T a).re hclose).trans (mul_le_mul_of_nonneg_left hsq hC.le)
    exact cusp_ratio_lower hC.le hy_pos hy_le hx
  exact tendsto_atTop_mono' l hbound hlower

theorem farey_vertex_ratio_tendsto_atTop {α : Type*} {l : Filter α}
    (levels : ℤ → ℕ) (r : ℝ) (hr0 : pastedFareyHeight levels r = 0)
    (T : α → ℂ) (hT : Tendsto T l (𝓝 (r : ℂ)))
    (hdom : ∀ᶠ a in l, T a ∈ upperGraphDomain (pastedFareyHeight levels)) :
    Tendsto (fun a => (T a).im / (((T a).re - r) ^ 2 + (T a).im ^ 2)) l atTop := by
  apply farey_vertex_ratio_closed_tendsto_atTop levels r hr0 T hT
  filter_upwards [hdom] with a ha
  exact ⟨ha.le, (pastedFareyHeight_nonneg levels (T a).re).trans_lt ha⟩

end ThreeOmittedValues
