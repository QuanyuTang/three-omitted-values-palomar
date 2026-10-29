module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic

/-!
# Closing a real-line curve at its common limit

A continuous curve of bounded variation on the real line, with the same
limit at both ends, can be parametrized continuously on a compact interval
by inserting that common limit at its two endpoints.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace ThreeOmittedValues

noncomputable def closeRealCurve (G : ℝ → ℂ) (p : ℂ) (t : ℝ) : ℂ :=
  if t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) then G (Real.tan t) else p

@[simp] theorem closeRealCurve_left (G : ℝ → ℂ) (p : ℂ) :
    closeRealCurve G p (-(Real.pi / 2)) = p := by simp [closeRealCurve]

@[simp] theorem closeRealCurve_right (G : ℝ → ℂ) (p : ℂ) :
    closeRealCurve G p (Real.pi / 2) = p := by simp [closeRealCurve]

theorem closeRealCurve_left_continuous {G : ℝ → ℂ} {p : ℂ}
    (hbot : Tendsto G atBot (𝓝 p)) :
    ContinuousWithinAt (closeRealCurve G p) (Ici (-(Real.pi / 2))) (-(Real.pi / 2)) := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Tendsto (closeRealCurve G p) (𝓝[>] (-(Real.pi / 2)))
    (𝓝 (closeRealCurve G p (-(Real.pi / 2))))
  rw [closeRealCurve_left]
  have hlt : -(Real.pi / 2) < Real.pi / 2 := by linarith [Real.pi_pos]
  have heq : closeRealCurve G p =ᶠ[𝓝[>] (-(Real.pi / 2))] (G ∘ Real.tan) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with t htleft htright
    have ht : t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨htleft, htright⟩
    simp [closeRealCurve, ht]
  exact Filter.Tendsto.congr' heq.symm (hbot.comp Real.tendsto_tan_neg_pi_div_two)

theorem closeRealCurve_right_continuous {G : ℝ → ℂ} {p : ℂ}
    (htop : Tendsto G atTop (𝓝 p)) :
    ContinuousWithinAt (closeRealCurve G p) (Iic (Real.pi / 2)) (Real.pi / 2) := by
  apply continuousWithinAt_Iio_iff_Iic.mp
  change Tendsto (closeRealCurve G p) (𝓝[<] (Real.pi / 2))
    (𝓝 (closeRealCurve G p (Real.pi / 2)))
  rw [closeRealCurve_right]
  have hlt : -(Real.pi / 2) < Real.pi / 2 := by linarith [Real.pi_pos]
  have heq : closeRealCurve G p =ᶠ[𝓝[<] (Real.pi / 2)] (G ∘ Real.tan) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hlt)] with t htright htleft
    have ht : t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨htleft, htright⟩
    simp [closeRealCurve, ht]
  exact Filter.Tendsto.congr' heq.symm (htop.comp Real.tendsto_tan_pi_div_two)

theorem closeRealCurve_continuousOn {G : ℝ → ℂ} {p : ℂ}
    (hG : Continuous G) (hbot : Tendsto G atBot (𝓝 p)) (htop : Tendsto G atTop (𝓝 p)) :
    ContinuousOn (closeRealCurve G p) (Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  intro t ht
  by_cases hl : t = -(Real.pi / 2)
  · subst t
    exact (closeRealCurve_left_continuous hbot).mono Icc_subset_Ici_self
  by_cases hr : t = Real.pi / 2
  · subst t
    exact (closeRealCurve_right_continuous htop).mono Icc_subset_Iic_self
  have htI : t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm hl), lt_of_le_of_ne ht.2 hr⟩
  have htan : ContinuousAt Real.tan t :=
    Real.continuousOn_tan_Ioo.continuousAt (isOpen_Ioo.mem_nhds htI)
  have heq : closeRealCurve G p =ᶠ[𝓝 t] (G ∘ Real.tan) := by
    filter_upwards [isOpen_Ioo.mem_nhds htI] with u hu
    simp [closeRealCurve, hu]
  exact ((hG.continuousAt.comp htan).congr_of_eventuallyEq heq).continuousWithinAt

theorem closeRealCurve_boundedVariation {G : ℝ → ℂ} {p : ℂ}
    (hvar : BoundedVariationOn G univ)
    (hbot : Tendsto G atBot (𝓝 p)) (htop : Tendsto G atTop (𝓝 p)) :
    BoundedVariationOn (closeRealCurve G p) (Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  let a := -(Real.pi / 2)
  let b := Real.pi / 2
  let γ := closeRealCurve G p
  have hab : a < b := by dsimp [a, b]; linarith [Real.pi_pos]
  have hleft : ContinuousWithinAt γ (Ici a) a := closeRealCurve_left_continuous hbot
  have hright : ContinuousWithinAt γ (Iic b) b := closeRealCurve_right_continuous htop
  have hne : (𝓝[Iio b ∩ Ioi a] a).NeBot := by
    have hnb : (𝓝[>] a).NeBot := by infer_instance
    convert hnb using 1
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab))
  have hLeftVar : eVariationOn γ (Ioo a b) = eVariationOn γ (Ico a b) := by
    have h := eVariationOn.eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
      hne (hleft.mono inter_subset_right)
    have h1 : Iio b ∩ Ioi a = Ioo a b := by ext x; simp [and_comm]
    have h2 : Iio b ∩ Ici a = Ico a b := by ext x; simp [and_comm]
    simpa only [h1, h2] using h
  have hRightVar : eVariationOn γ (Ico a b) = eVariationOn γ (Icc a b) :=
    eVariationOn.eVariationOn_Ico_eq_Icc_of_continuousWithinAt hright
  have hEq : EqOn γ (G ∘ Real.tan) (Ioo a b) := by
    intro x hx
    simp [γ, closeRealCurve, a, b, hx]
  have hmono : MonotoneOn Real.tan (Ioo a b) := Real.strictMonoOn_tan.monotoneOn
  have hvarOpen : eVariationOn γ (Ioo a b) ≤ eVariationOn G univ := by
    rw [eVariationOn.congr hEq]
    exact eVariationOn.comp_le_of_monotoneOn G Real.tan hmono (mapsTo_univ _ _)
  apply ne_top_of_le_ne_top hvar
  rw [← hRightVar, ← hLeftVar]
  exact hvarOpen

end ThreeOmittedValues
