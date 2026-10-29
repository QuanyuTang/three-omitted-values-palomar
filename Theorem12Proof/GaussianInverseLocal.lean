module

public import Theorem12Proof.GaussianBoundaryGraph
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# Local inversion above the Gaussian boundary

A contraction on a disk above a real boundary point gives a preimage of
every point vertically above its boundary image. The disk also supplies a
quantitative lower bound for the preimage's imaginary part.
-/

@[expose] public section

open Complex Metric MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal MeasureTheory ProbabilityTheory Topology

namespace ThreeOmittedValues

theorem scaled_gaussianKernel_lipschitz {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    ‖(gaussianScale : ℂ) * (gaussianKernel z - gaussianKernel w)‖ ≤
      (1 / 4 : ℝ) * ‖z - w‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos gaussianScale_pos]
  calc
    gaussianScale * ‖gaussianKernel z - gaussianKernel w‖ ≤
        gaussianScale * (gaussianMoment * ‖z - w‖) :=
      mul_le_mul_of_nonneg_left (gaussianKernel_lipschitz_upper hz hw) gaussianScale_pos.le
    _ = (gaussianScale * gaussianMoment) * ‖z - w‖ := by ring
    _ ≤ (1 / 4 : ℝ) * ‖z - w‖ :=
      mul_le_mul_of_nonneg_right gaussianScale_mul_moment_le_quarter (norm_nonneg _)

theorem gaussianPerturbation_vertical_inverse (t h : ℝ) (hh : 0 < h) :
    ∃ z : ℂ, 0 < z.im ∧
      gaussianPerturbation z = gaussianPerturbation (t : ℂ) + (h : ℂ) * Complex.I ∧
      ‖z - ((t : ℂ) + (h : ℂ) * Complex.I)‖ ≤ h / 2 := by
  let c : ℂ := (t : ℂ) + (h : ℂ) * Complex.I
  let S : Set ℂ := closedBall c (h / 2)
  let T : ℂ → ℂ := fun z => gaussianPerturbation (t : ℂ) + (h : ℂ) * Complex.I -
    (gaussianScale : ℂ) * gaussianKernel z
  have hcim : c.im = h := by simp [c]
  have hcbase : ‖c - (t : ℂ)‖ = h := by
    simp [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hS_im (z : ℂ) (hz : z ∈ S) : h / 2 ≤ z.im := by
    have hn : ‖z - c‖ ≤ h / 2 := by simpa [S, dist_eq_norm] using hz
    have hi := Complex.abs_im_le_norm (z - c)
    simp only [Complex.sub_im, hcim] at hi
    have hi' := (abs_le.mp (hi.trans hn)).1
    linarith
  have hSbase (z : ℂ) (hz : z ∈ S) : ‖z - (t : ℂ)‖ ≤ h / 2 + h := by
    have hn : ‖z - c‖ ≤ h / 2 := by simpa [S, dist_eq_norm] using hz
    calc
      ‖z - (t : ℂ)‖ = ‖(z - c) + (c - (t : ℂ))‖ := by congr 1 <;> ring
      _ ≤ ‖z - c‖ + ‖c - (t : ℂ)‖ := norm_add_le _ _
      _ ≤ h / 2 + h := by rw [hcbase]; linarith
  have hmap : MapsTo T S S := by
    intro z hz
    have him : 0 ≤ z.im := by have := hS_im z hz; linarith
    have hs := scaled_gaussianKernel_lipschitz (z := (t : ℂ)) (w := z) (by simp) him
    have hbase := hSbase z hz
    have heq : T z - c = (gaussianScale : ℂ) *
        (gaussianKernel (t : ℂ) - gaussianKernel z) := by
      simp only [T, c, gaussianPerturbation]
      ring
    change dist (T z) c ≤ h / 2
    rw [dist_eq_norm, heq]
    have hn : ‖(t : ℂ) - z‖ = ‖z - (t : ℂ)‖ := norm_sub_rev _ _
    rw [hn] at hs
    nlinarith
  have hcontract : ContractingWith (⟨(1 / 4 : ℝ), by norm_num⟩ : ℝ≥0)
      (hmap.restrict T S S) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
    · change (1 / 4 : ℝ) < 1
      norm_num
    · intro z w
      change dist (T z.1) (T w.1) ≤ (1 / 4 : ℝ) * dist z.1 w.1
      rw [dist_eq_norm, dist_eq_norm]
      have hz : 0 ≤ z.1.im := by have := hS_im z.1 z.2; linarith
      have hw : 0 ≤ w.1.im := by have := hS_im w.1 w.2; linarith
      have heq : T z.1 - T w.1 = -((gaussianScale : ℂ) *
          (gaussianKernel z.1 - gaussianKernel w.1)) := by
        simp only [T]
        ring
      rw [heq, norm_neg]
      exact scaled_gaussianKernel_lipschitz hz hw
  have hcS : c ∈ S := by
    dsimp [S]
    exact mem_closedBall_self (by positivity)
  obtain ⟨z, hzS, hzfix, _htend, _hbound⟩ :=
    ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete hmap hcontract hcS
      (edist_ne_top _ _)
  refine ⟨z, ?_, ?_, ?_⟩
  · have := hS_im z hzS
    linarith
  · change T z = z at hzfix
    simp only [T, gaussianPerturbation] at hzfix ⊢
    linear_combination -hzfix
  · simpa [S, c, dist_eq_norm] using hzS

end ThreeOmittedValues
