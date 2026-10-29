module

public import Theorem12Proof.GaussianInverseLocal
public import Theorem12Proof.GaussianImageContainment
public import Theorem12Proof.GraphTopology
public import Theorem12Proof.HalfPlaneWeight
import Mathlib.Tactic

/-!
# The Gaussian comparison domain and a quantitative inverse bound

The perturbation maps the upper half-plane exactly onto the epigraph of its
Gaussian boundary graph. Above twice the boundary height, a preimage retains
a fixed proportion of the target's half-plane Blaschke weight.
-/

@[expose] public section

open Complex Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem gaussian_graph_inverse {w : ℂ} (hw : gaussianBeta w.re < w.im) :
    ∃ z : ℂ, 0 < z.im ∧ gaussianPerturbation z = w ∧
      (w.im - gaussianBeta w.re) / 2 ≤ z.im ∧
      |z.re - w.re| ≤ gaussianScale + (w.im - gaussianBeta w.re) / 2 ∧
      z.im ≤ 3 * (w.im - gaussianBeta w.re) / 2 := by
  let t := gaussianBoundaryHomeomorph.symm w.re
  let h := w.im - gaussianBeta w.re
  have hh : 0 < h := by dsimp [h]; linarith
  have hx : gaussianBoundaryX t = w.re := by
    rw [← gaussianBoundaryHomeomorph_apply, Homeomorph.apply_symm_apply]
  obtain ⟨z, hz, himage, hnear⟩ := gaussianPerturbation_vertical_inverse t h hh
  have himage' : gaussianPerturbation z = w := by
    rw [himage, gaussian_boundary_point]
    apply Complex.ext <;> simp [h]
  have hre := (Complex.abs_re_le_norm (z - ((t : ℂ) + (h : ℂ) * Complex.I))).trans hnear
  have him := (Complex.abs_im_le_norm (z - ((t : ℂ) + (h : ℂ) * Complex.I))).trans hnear
  have hreal : |z.re - t| ≤ h / 2 := by simpa using hre
  have himag : |z.im - h| ≤ h / 2 := by simpa using him
  have htx : |t - w.re| ≤ gaussianScale := by
    have hclose := gaussianBoundaryX_close t
    rw [hx] at hclose
    simpa [abs_sub_comm] using hclose
  have hreal' : |z.re - w.re| ≤ gaussianScale + h / 2 := by
    calc
      |z.re - w.re| = |(z.re - t) + (t - w.re)| := by congr 1 <;> ring
      _ ≤ |z.re - t| + |t - w.re| := abs_add_le _ _
      _ ≤ gaussianScale + h / 2 := by linarith
  refine ⟨z, hz, himage', ?_, ?_, ?_⟩
  · have := (abs_le.mp himag).1
    dsimp [h] at *
    linarith
  · simpa [h] using hreal'
  · have := (abs_le.mp himag).2
    dsimp [h] at *
    linarith

theorem gaussianPerturbation_image_upper :
    gaussianPerturbation '' {z : ℂ | 0 < z.im} = upperGraphDomain gaussianBeta := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact gaussianPerturbation_image_above_graph hz
  · intro hw
    obtain ⟨z, hz, heq, _⟩ := gaussian_graph_inverse hw
    exact ⟨z, hz, heq⟩

theorem gaussian_inverse_weight {w : ℂ} (hw1 : w.im ≤ 1)
    (hwβ : gaussianBeta w.re ≤ w.im / 2) :
    ∃ z : ℂ, 0 < z.im ∧ gaussianPerturbation z = w ∧
      w.im / (32 * (1 + w.re ^ 2)) ≤ blaschkeWeight z := by
  have hwpos : 0 < w.im := by have := gaussianBeta_pos w.re; linarith
  have hw : gaussianBeta w.re < w.im := by linarith
  obtain ⟨z, hz, heq, himlo, hreal, himhi⟩ := gaussian_graph_inverse hw
  have hβpos := gaussianBeta_pos w.re
  have hzlo : w.im / 4 ≤ z.im := by linarith
  have hzhi : z.im ≤ 3 / 2 := by linarith
  have hdist : |z.re - w.re| ≤ 1 := by
    have := gaussianScale_le_quarter
    linarith
  have hdiffsq : (z.re - w.re) ^ 2 ≤ 1 := by
    have h := abs_le.mp hdist
    nlinarith
  have hresq : z.re ^ 2 ≤ 2 * w.re ^ 2 + 2 := by
    nlinarith [sq_nonneg (z.re - 2 * w.re)]
  have himsq : z.im ^ 2 ≤ 9 / 4 := by nlinarith
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hden : 1 + ‖z‖ ^ 2 ≤ 8 * (1 + w.re ^ 2) := by
    rw [hnorm]
    nlinarith [sq_nonneg w.re]
  refine ⟨z, hz, heq, ?_⟩
  rw [blaschkeWeight, abs_of_pos hz]
  apply (div_le_div_iff₀ (by positivity : 0 < 32 * (1 + w.re ^ 2))
    (by positivity : 0 < 1 + ‖z‖ ^ 2)).2
  have hmul1 := mul_le_mul_of_nonneg_left hden hwpos.le
  have hmul2 := mul_le_mul_of_nonneg_left hzlo (show 0 ≤ 32 * (1 + w.re ^ 2) by positivity)
  nlinarith

end ThreeOmittedValues
