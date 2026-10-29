module

public import Theorem12Proof.FareyGlobalProperties
public import Theorem12Proof.FareyCuspFamilies
public import Theorem12Proof.MeromorphicCuspClassification
import Mathlib.Tactic

/-!
# The three exceptional fibres are real and infinite
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set Filter NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold Topology

namespace ThreeOmittedValues

theorem fareyGlobalExtension_eventually_ne_zero {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ) :
    ∀ᶠ z in 𝓝[≠] (x : ℂ), fareyGlobalExtension e z ≠ 0 := by
  obtain ⟨r, hr, _, homit⟩ := fareyReflected_punctured_omission hupper hΦ hΦimage e he he1 x
  have hball : ∀ᶠ z in 𝓝[≠] (x : ℂ), z ∈ ball (x : ℂ) r :=
    nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hr)
  filter_upwards [fareyGlobalExtension_eventuallyEq hupper hΦ hΦimage e he he1 (x : ℂ),
    hball, eventually_mem_nhdsWithin] with z heq hzball hzne
  rw [heq]
  exact (homit z ⟨hzball, hzne⟩).1

theorem fareyGlobalExtension_exceptional_fibres {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hlevels : ∀ n, 1 ≤ levels n)
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) :
    finiteValueFiber (fareyGlobalExtension e) 0 ⊆ {z : ℂ | z.im = 0} ∧
    finiteValueFiber (fareyGlobalExtension e) 1 ⊆ {z : ℂ | z.im = 0} ∧
    poleFiber (fareyGlobalExtension e) ⊆ {z : ℂ | z.im = 0} ∧
    (finiteValueFiber (fareyGlobalExtension e) 0).Infinite ∧
    (finiteValueFiber (fareyGlobalExtension e) 1).Infinite ∧
    (poleFiber (fareyGlobalExtension e)).Infinite := by
  let F := fareyGlobalExtension e
  let B : ℝ → ℂ := fun x => halfPlaneContinuousExtension e (x : ℂ)
  have hNF (z : ℂ) : MeromorphicNFAt F z :=
    fareyGlobalExtension_normalForm e (show z ∈ Set.univ by simp)
  have hfamilies := farey_three_cusp_families hlevels hupper hΦimage e he he1
  have hzero : ∀ n : ℕ, ∃ x : ℝ,
      B x = (((2 * (n : ℝ) + 1 / 2 : ℝ)) : ℂ) ∧ (x : ℂ) ∈ finiteValueFiber F 0 := by
    intro n
    obtain ⟨⟨x, hx, hlim⟩, _, _⟩ := hfamilies (n : ℤ)
    refine ⟨x, ?_, ?_⟩
    · simpa [B] using hx
    · apply finite_fibre_of_punctured_limit (hNF (x : ℂ))
      exact hlim.congr' (fareyGlobalExtension_eventuallyEq hupper hΦ hΦimage e he he1 (x : ℂ)).symm
  have hone : ∀ n : ℕ, ∃ x : ℝ,
      B x = (((2 * (n : ℝ) : ℝ)) : ℂ) ∧ (x : ℂ) ∈ finiteValueFiber F 1 := by
    intro n
    obtain ⟨_, ⟨x, hx, hlim⟩, _⟩ := hfamilies (n : ℤ)
    refine ⟨x, ?_, ?_⟩
    · simpa [B] using hx
    · apply one_fibre_of_normalized_limit (hNF (x : ℂ))
      apply hlim.congr'
      filter_upwards [(fareyGlobalExtension_eventuallyEq hupper hΦ hΦimage e he he1 (x : ℂ)).symm] with z hz
      simp [hz, F]
  have hpole : ∀ n : ℕ, ∃ x : ℝ,
      B x = (((2 * (n : ℝ) + 1 : ℝ)) : ℂ) ∧ (x : ℂ) ∈ poleFiber F := by
    intro n
    obtain ⟨_, _, ⟨x, hx, hlim⟩⟩ := hfamilies (n : ℤ)
    refine ⟨x, ?_, ?_⟩
    · simpa [B] using hx
    · apply pole_fibre_of_inverse_limit (hNF (x : ℂ))
        (fareyGlobalExtension_eventually_ne_zero hupper hΦ hΦimage e he he1 x)
      apply hlim.congr'
      filter_upwards [(fareyGlobalExtension_eventuallyEq hupper hΦ hΦimage e he he1 (x : ℂ)).symm] with z hz
      simp [hz, F]
  have hinj (c : ℝ) : Function.Injective (fun n : ℕ => ((2 * (n : ℝ) + c : ℝ) : ℂ)) := by
    intro m n h
    have hr := Complex.ofReal_injective h
    have hmn : (m : ℝ) = (n : ℝ) := by linarith
    exact_mod_cast hmn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    by_contra hne
    exact (fareyGlobalExtension_off_real hupper hΦ hΦimage e he he1 hne).2.2.1 hz.2
  · intro z hz
    by_contra hne
    exact (fareyGlobalExtension_off_real hupper hΦ hΦimage e he he1 hne).2.2.2 hz.2
  · intro z hz
    by_contra hne
    exact hz (fareyGlobalExtension_off_real hupper hΦ hΦimage e he he1 hne).1
  · exact infinite_fibre_of_injective_parameters B _ _ (hinj (1 / 2)) hzero
  · apply infinite_fibre_of_injective_parameters B _ (fun n : ℕ => ((2 * (n : ℝ) : ℝ) : ℂ))
    · simpa using hinj 0
    · exact hone
  · exact infinite_fibre_of_injective_parameters B _ _ (hinj 1) hpole

end ThreeOmittedValues
