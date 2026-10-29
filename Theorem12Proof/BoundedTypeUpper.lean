module

public import Theorem12Proof.BoundedQuotient
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic

/-!
# A non-Blaschke fibre excludes bounded type

The quotient definition below only asks for equality where its denominator
is nonzero, which is sufficient for a meromorphic quotient and also covers
the total-function conventions used at poles.
-/

@[expose] public section

open Complex Metric Set Filter
open scoped Topology

namespace ThreeOmittedValues

def IsBoundedTypeOnUpper (F : ℂ → ℂ) : Prop :=
  ∃ (u v : ℂ → ℂ) (Cu Cv : ℝ),
    AnalyticOnNhd ℂ u {z : ℂ | 0 < z.im} ∧
    AnalyticOnNhd ℂ v {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 < z.im → ‖u z‖ ≤ Cu) ∧
    (∀ z : ℂ, 0 < z.im → ‖v z‖ ≤ Cv) ∧
    (∃ z : ℂ, 0 < z.im ∧ v z ≠ 0) ∧
    (∀ z : ℂ, 0 < z.im → v z ≠ 0 → F z = u z / v z)

/-- If `F` takes a different finite value at an analytic point, any
nonzero analytic denominator is nonzero at some nearby such point. -/
theorem exists_distinct_value_off_denominator_zeros {F v : ℂ → ℂ} {target b : ℂ}
    (hv : AnalyticOnNhd ℂ v {z : ℂ | 0 < z.im})
    (hvnon : ∃ z : ℂ, 0 < z.im ∧ v z ≠ 0)
    (hb : 0 < b.im) (hFb : AnalyticAt ℂ F b) (hFne : F b ≠ target) :
    ∃ z : ℂ, 0 < z.im ∧ v z ≠ 0 ∧ F z ≠ target := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUevent : ∀ᶠ z in 𝓝 b, 0 < z.im := hU.mem_nhds hb
  have hFevent : ∀ᶠ z in 𝓝 b, F z ≠ target := by
    have hopen : IsOpen ({target}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
    have hmem : F b ∈ ({target}ᶜ : Set ℂ) := by simpa using hFne
    exact hFb.continuousAt.tendsto.eventually (hopen.mem_nhds hmem)
  by_contra hnot
  have hvzero : v =ᶠ[𝓝 b] 0 := by
    filter_upwards [hUevent, hFevent] with z hz hFz
    change v z = 0
    by_contra hvz
    exact hnot ⟨z, hz, hvz, hFz⟩
  have hall : EqOn v 0 {z : ℂ | 0 < z.im} :=
    hv.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_im_gt 0).isPreconnected hb hvzero
  obtain ⟨p, hp, hpv⟩ := hvnon
  exact hpv (by simpa using hall hp)

/-- A non-Blaschke family in one finite fibre rules out bounded type,
provided the function takes a different value at an analytic point. -/
theorem not_boundedType_upper_of_nonsummable_fiber {ι : Type*} (a : ι → ℂ)
    (ha : Function.Injective a) {F : ℂ → ℂ} {target : ℂ}
    (hpoints : ∀ i, 0 < (a i).im ∧ F (a i) = target)
    (hdivergent : ¬ Summable (fun i => blaschkeWeight (a i)))
    (hdistinct : ∃ b : ℂ, 0 < b.im ∧ AnalyticAt ℂ F b ∧ F b ≠ target) :
    ¬ IsBoundedTypeOnUpper F := by
  rintro ⟨u, v, Cu, Cv, hu, hv, hub, hvb, hvnon, hratio⟩
  obtain ⟨b, hb, hFb, hFne⟩ := hdistinct
  have hdifferent := exists_distinct_value_off_denominator_zeros hv hvnon hb hFb hFne
  exact hdivergent (summable_quotient_fiber_weights a ha hu hv hub hvb hvnon hratio
    hdifferent hpoints)

end ThreeOmittedValues
