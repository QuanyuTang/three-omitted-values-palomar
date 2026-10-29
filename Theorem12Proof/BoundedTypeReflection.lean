module

public import Theorem12Proof.BoundedTypeUpper
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic

/-!
# Reflection of bounded type

For a real-symmetric function, a bounded quotient representation on the
lower half-plane reflects to one on the upper half-plane.
-/

@[expose] public section

open Complex Metric Set

namespace ThreeOmittedValues

def IsBoundedTypeOnLower (F : ℂ → ℂ) : Prop :=
  ∃ (u v : ℂ → ℂ) (Cu Cv : ℝ),
    AnalyticOnNhd ℂ u {z : ℂ | z.im < 0} ∧
    AnalyticOnNhd ℂ v {z : ℂ | z.im < 0} ∧
    (∀ z : ℂ, z.im < 0 → ‖u z‖ ≤ Cu) ∧
    (∀ z : ℂ, z.im < 0 → ‖v z‖ ≤ Cv) ∧
    (∃ z : ℂ, z.im < 0 ∧ v z ≠ 0) ∧
    (∀ z : ℂ, z.im < 0 → v z ≠ 0 → F z = u z / v z)

def reflectedFunction (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (f ((starRingEnd ℂ) z))

theorem analytic_reflected_lower_to_upper {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | z.im < 0}) :
    AnalyticOnNhd ℂ (reflectedFunction f) {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_im)
  intro z hz
  have hz' : ((starRingEnd ℂ) z).im < 0 := by simpa using neg_neg_of_pos hz
  have hd := (hf _ hz').differentiableAt.conj_conj
  apply DifferentiableAt.differentiableWithinAt
  simpa only [reflectedFunction, Function.comp_def, Complex.conj_conj] using! hd

theorem boundedType_upper_of_lower_of_realSymmetric {F : ℂ → ℂ}
    (hsym : ∀ z, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z))
    (hF : IsBoundedTypeOnLower F) : IsBoundedTypeOnUpper F := by
  obtain ⟨u, v, Cu, Cv, hu, hv, hub, hvb, hvnon, hratio⟩ := hF
  refine ⟨reflectedFunction u, reflectedFunction v, Cu, Cv,
    analytic_reflected_lower_to_upper hu, analytic_reflected_lower_to_upper hv, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hz' : ((starRingEnd ℂ) z).im < 0 := by simpa using neg_neg_of_pos hz
    simpa only [reflectedFunction, Complex.norm_conj] using hub ((starRingEnd ℂ) z) hz'
  · intro z hz
    have hz' : ((starRingEnd ℂ) z).im < 0 := by simpa using neg_neg_of_pos hz
    simpa only [reflectedFunction, Complex.norm_conj] using hvb ((starRingEnd ℂ) z) hz'
  · obtain ⟨z, hz, hvz⟩ := hvnon
    refine ⟨(starRingEnd ℂ) z, ?_, ?_⟩
    · simpa using neg_pos.mpr hz
    · simpa [reflectedFunction] using hvz
  · intro z hz hvz
    have hz' : ((starRingEnd ℂ) z).im < 0 := by simpa using neg_neg_of_pos hz
    have hvz' : v ((starRingEnd ℂ) z) ≠ 0 := by
      intro h
      apply hvz
      simp [reflectedFunction, h]
    have heq := congrArg (starRingEnd ℂ) (hratio ((starRingEnd ℂ) z) hz' hvz')
    simpa [reflectedFunction, hsym] using heq

theorem not_boundedType_lower_of_upper_of_realSymmetric {F : ℂ → ℂ}
    (hsym : ∀ z, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z))
    (hupper : ¬ IsBoundedTypeOnUpper F) : ¬ IsBoundedTypeOnLower F :=
  fun hlower => hupper (boundedType_upper_of_lower_of_realSymmetric hsym hlower)

end ThreeOmittedValues
