module

public import Theorem12Proof.FareyPuncturedAnalytic
import Mathlib.Tactic

/-!
# The reflected composite omits `0` and `1` near punctures

The punctured neighborhoods contain only upper-half-plane values of the
modular function and their conjugates, including on the reflected edges.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem fareyReflected_omits_of_nonvertex {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    {z : ℂ} (hreal : z.im = 0 → 0 < (halfPlaneContinuousExtension e z).im) :
    fareyReflectedComposite e z ≠ 0 ∧ fareyReflectedComposite e z ≠ 1 := by
  have hΦpos (w : ℂ) (hw : 0 < w.im) : 0 < (Φ w).im :=
    hupper (by rw [← hΦimage]; exact ⟨w, hw, rfl⟩)
  by_cases hp : 0 < z.im
  · rw [fareyReflectedComposite, schwarzReflect_apply_of_im_nonneg _ hp.le,
      halfPlaneContinuousExtension_interior hupper hΦimage e he hp]
    exact ⟨modularLambdaH_ne_zero (hΦpos z hp), modularLambdaH_ne_one (hΦpos z hp)⟩
  · by_cases hn : z.im < 0
    · have hc : 0 < ((starRingEnd ℂ) z).im := by simp; linarith
      rw [fareyReflectedComposite, schwarzReflect_apply_of_im_neg _ hn,
        halfPlaneContinuousExtension_interior hupper hΦimage e he hc]
      have h0 := modularLambdaH_ne_zero (hΦpos _ hc)
      have h1 := modularLambdaH_ne_one (hΦpos _ hc)
      constructor
      · intro h
        apply h0
        have hh := congrArg (starRingEnd ℂ) h
        simpa using hh
      · intro h
        apply h1
        have hh := congrArg (starRingEnd ℂ) h
        simpa using hh
    · have hz0 : z.im = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      rw [fareyReflectedComposite, schwarzReflect_apply_of_im_nonneg _ hz0.ge]
      exact ⟨modularLambdaH_ne_zero (hreal hz0), modularLambdaH_ne_one (hreal hz0)⟩

theorem fareyReflected_punctured_omission {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ) :
    ∃ r : ℝ, 0 < r ∧ DifferentiableOn ℂ (fareyReflectedComposite e)
      (ball (x : ℂ) r \ {(x : ℂ)}) ∧
      ∀ z ∈ ball (x : ℂ) r \ {(x : ℂ)},
        fareyReflectedComposite e z ≠ 0 ∧ fareyReflectedComposite e z ≠ 1 := by
  obtain ⟨r, hr, hisol⟩ := farey_preimage_vertex_isolated hΦimage e he he1 x
  obtain ⟨s, hs, hdiff⟩ := fareyReflected_punctured_holomorphic hupper hΦ hΦimage e he he1 x
  refine ⟨min r s, lt_min hr hs, hdiff.mono ?_, ?_⟩
  · exact sdiff_subset_sdiff_left (ball_subset_ball (min_le_right _ _))
  · intro z hz
    apply fareyReflected_omits_of_nonvertex hupper hΦimage e he
    intro hz0
    have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
    have hzball : z.re ∈ ball x r := by
      have hd : ‖z - (x : ℂ)‖ < r := by
        have h := (ball_subset_ball (min_le_left r s)) hz.1
        simpa [mem_ball, dist_eq_norm] using h
      have h := (Complex.abs_re_le_norm (z - (x : ℂ))).trans_lt hd
      simpa [mem_ball, Real.dist_eq] using h
    have hbar_ne : (halfPlaneContinuousExtension e z).im ≠ 0 := by
      intro hzero
      have hzero' : (halfPlaneContinuousExtension e (z.re : ℂ)).im = 0 := by
        rw [← hzreal]
        exact hzero
      have hxr := hisol z.re hzball hzero'
      have hzeq : z = (x : ℂ) := by rw [hzreal, hxr]
      exact hz.2 (by simpa [hzeq])
    obtain ⟨u, hu⟩ := halfPlaneContinuousExtension_boundary hΦimage e he he1 hz0
    have hbar_nonneg : 0 ≤ (halfPlaneContinuousExtension e z).im := by
      rw [hu]
      simpa [graphMap] using pastedFareyHeight_nonneg levels u
    exact lt_of_le_of_ne hbar_nonneg (Ne.symm hbar_ne)

end ThreeOmittedValues
