module

public import Theorem12Proof.MeromorphicFibres
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic

/-!
# Analytic fibres under real reflection

The proof uses the local analyticity of a fibre point. It does not identify
the full reflected multiplicity function.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ThreeOmittedValues

/-- A real-symmetric function is analytic at the conjugate of every point
where it is analytic. -/
theorem analyticAt_conj_of_realSymmetric {f : ℂ → ℂ} {z : ℂ}
    (hsym : ∀ u, f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (f u))
    (hz : AnalyticAt ℂ f z) : AnalyticAt ℂ f ((starRingEnd ℂ) z) := by
  have hfun : (starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ) = f := by
    funext u
    simp only [Function.comp_apply, hsym, Complex.conj_conj]
  have hevent : ∀ᶠ u in 𝓝 z, DifferentiableAt ℂ f u :=
    Complex.analyticAt_iff_eventually_differentiableAt.mp hz
  have hcont : Tendsto (starRingEnd ℂ) (𝓝 ((starRingEnd ℂ) z)) (𝓝 z) := by
    have hcoe : (Complex.conjCLE : ℂ → ℂ) = fun u => (starRingEnd ℂ) u := by
      funext u
      exact Complex.conjCLE_apply u
    simpa only [hcoe, Complex.conj_conj] using
      (Complex.conjCLE.continuous.tendsto ((starRingEnd ℂ) z))
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [hcont.eventually hevent] with u hu
  have hreflected := hu.conj_conj
  simpa only [Complex.conj_conj, hfun] using hreflected

/-- A finite fibre of a real-symmetric function reflects to the conjugate
finite fibre, with analyticity retained. -/
theorem finiteValueFiber_conj_of_realSymmetric {f : ℂ → ℂ} {a z : ℂ}
    (hsym : ∀ u, f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (f u))
    (hz : z ∈ finiteValueFiber f a) :
    (starRingEnd ℂ) z ∈ finiteValueFiber f ((starRingEnd ℂ) a) := by
  constructor
  · exact analyticAt_conj_of_realSymmetric hsym hz.1
  · rw [hsym, hz.2]

end ThreeOmittedValues
