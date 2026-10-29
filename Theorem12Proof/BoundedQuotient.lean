module

public import Theorem12Proof.HalfPlaneBlaschke
import Mathlib.Tactic

/-!
# Fibres of quotients of bounded analytic functions

This proves the bounded-type implication needed in the paper. It allows the
denominator to vanish at points of the selected fibre: those points form a
second Blaschke-summable zero family.
-/

@[expose] public section

open Complex Metric Set

namespace ThreeOmittedValues

theorem summable_quotient_fiber_weights {ι : Type*} (a : ι → ℂ)
    (ha : Function.Injective a) {F u v : ℂ → ℂ} {target : ℂ} {Cu Cv : ℝ}
    (hu : AnalyticOnNhd ℂ u {z : ℂ | 0 < z.im})
    (hv : AnalyticOnNhd ℂ v {z : ℂ | 0 < z.im})
    (hub : ∀ z : ℂ, 0 < z.im → ‖u z‖ ≤ Cu)
    (hvb : ∀ z : ℂ, 0 < z.im → ‖v z‖ ≤ Cv)
    (hvnon : ∃ z : ℂ, 0 < z.im ∧ v z ≠ 0)
    (hratio : ∀ z : ℂ, 0 < z.im → v z ≠ 0 → F z = u z / v z)
    (hdifferent : ∃ z : ℂ, 0 < z.im ∧ v z ≠ 0 ∧ F z ≠ target)
    (hpoints : ∀ i, 0 < (a i).im ∧ F (a i) = target) :
    Summable (fun i => blaschkeWeight (a i)) := by
  classical
  let w : ℂ → ℂ := fun z => u z - target * v z
  have hw : AnalyticOnNhd ℂ w {z : ℂ | 0 < z.im} := by
    intro z hz
    exact (hu z hz).sub (analyticAt_const.mul (hv z hz))
  have hwb : ∀ z : ℂ, 0 < z.im → ‖w z‖ ≤ Cu + ‖target‖ * Cv := by
    intro z hz
    calc
      ‖w z‖ ≤ ‖u z‖ + ‖target * v z‖ := norm_sub_le _ _
      _ = ‖u z‖ + ‖target‖ * ‖v z‖ := by rw [norm_mul]
      _ ≤ Cu + ‖target‖ * Cv :=
        add_le_add (hub z hz) (mul_le_mul_of_nonneg_left (hvb z hz) (norm_nonneg target))
  have hwnon : ∃ z : ℂ, 0 < z.im ∧ w z ≠ 0 := by
    obtain ⟨z, hz, hvz, hFz⟩ := hdifferent
    refine ⟨z, hz, ?_⟩
    intro hwz
    have huval : u z = target * v z := sub_eq_zero.mp hwz
    have hdiv : u z / v z = target := (div_eq_iff hvz).2 huval
    exact hFz ((hratio z hz hvz).trans hdiv)
  let S : Set ι := {i | v (a i) = 0}
  have hS : Summable (fun i : S => blaschkeWeight (a i.1)) := by
    apply summable_halfPlane_zero_weights (fun i : S => a i.1) (ha.comp Subtype.val_injective)
      hv hvb hvnon
    intro i
    exact ⟨(hpoints i.1).1, i.2⟩
  have hSc : Summable (fun i : (Sᶜ : Set ι) => blaschkeWeight (a i.1)) := by
    apply summable_halfPlane_zero_weights (fun i : (Sᶜ : Set ι) => a i.1) (ha.comp Subtype.val_injective)
      hw hwb hwnon
    intro i
    have hvne : v (a i.1) ≠ 0 := i.2
    have hdiv : u (a i.1) / v (a i.1) = target :=
      (hratio (a i.1) (hpoints i.1).1 hvne).symm.trans (hpoints i.1).2
    have huval : u (a i.1) = target * v (a i.1) := (div_eq_iff hvne).1 hdiv
    refine ⟨(hpoints i.1).1, ?_⟩
    change u (a i.1) - target * v (a i.1) = 0
    rw [huval, sub_self]
  exact Summable.add_compl (s := S) hS hSc

end ThreeOmittedValues
