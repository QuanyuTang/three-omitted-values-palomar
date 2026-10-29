module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Complex
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic
public import Theorem12Proof.RequestProject.RiemannMappingInterior

/-!
# Minimal energy input for the conformal cap argument

These proofs are extracted from the prior Apache-2.0 Neumann development,
commit b37a190b8afc6efb128f204176d26deec8d88a8c, files
`LocalConformalH1.lean` and `RiemannMappingEnergy.lean`. The unrelated
Sobolev, spectral, and transport material has not been imported.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Real ContDiff ComplexConjugate Topology ENNReal

private theorem abs_det_complex_deriv (c : ℂ) :
    |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det| =
      ‖c‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars]
  simp [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

theorem localConformal_integrable_weight {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U) {a : ℂ → ℝ}
    (ha : IntegrableOn a (F '' U)) :
    IntegrableOn (fun z => ‖deriv F z‖ ^ 2 * a (F z)) U := by
  have hfd : ∀ z ∈ U, HasFDerivWithinAt F
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv F z)).restrictScalars ℝ) U z :=
    fun z hz => ((hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt
  have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    hU.measurableSet hfd hinj a).1 ha
  simpa only [abs_det_complex_deriv, smul_eq_mul] using h

/-- A univalent holomorphic map with bounded image has square-integrable
complex derivative on the disk. -/
theorem interiorConformal_deriv_sq_integrable (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    IntegrableOn (fun z => ‖deriv F z‖ ^ 2) (ball (0 : ℂ) 1) := by
  have hconst : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (F '' ball (0 : ℂ) 1) :=
    integrableOn_const hb.measure_lt_top.ne
  simpa only [mul_one] using localConformal_integrable_weight isOpen_ball hF hinj hconst

end PolyaNeumann

end
