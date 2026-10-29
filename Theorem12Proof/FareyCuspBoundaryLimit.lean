module

public import Theorem12Proof.FareyCuspMobius
public import Theorem12Proof.ModularCuspLimits
public import Theorem12Proof.FareyBoundaryVerticesDiscrete
import Mathlib.Tactic

/-!
# A normalized limit at each Farey vertex

Approaching a vertex from the closed upper half-plane, away from the vertex
itself, one of `λ`, `1 - λ`, or `1 / λ` tends to zero. The proof uses the
quantitative geometry of the graph and the uniform modular cusp limit.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set Filter NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold Topology

namespace ThreeOmittedValues

theorem farey_normalized_cusp_limit_closed_of_matrix {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x r : ℝ)
    (hr0 : pastedFareyHeight levels r = 0)
    (hrval : halfPlaneContinuousExtension e (x : ℂ) = (r : ℂ))
    (γ : SL(2, ℤ)) (p q : ℤ) (hq : 0 < q) (hr : r = (p : ℝ) / q)
    (h00 : γ.1 0 0 = p) (h10 : γ.1 1 0 = q) (k : Fin 6)
    (hk : ∀ τ : UpperHalfPlane,
      modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ) = lambdaTransform k (modularLambdaH (τ : ℂ))) :
    Tendsto (fun z => cuspNormalize k
      (modularLambdaH (halfPlaneContinuousExtension e z)))
      (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ)) (𝓝 0) := by
  obtain ⟨ρ, hρ, hisol⟩ := farey_preimage_vertex_isolated hΦimage e he he1 x
  let C : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let L : Filter ℂ := 𝓝[C \ {(x : ℂ)}] (x : ℂ)
  have hmem : ∀ᶠ z in L, z ∈ C \ {(x : ℂ)} := eventually_mem_nhdsWithin
  have hnear : ∀ᶠ z in L, z ∈ ball (x : ℂ) ρ :=
    nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hρ)
  have hpos : ∀ᶠ z in L, 0 < (halfPlaneContinuousExtension e z).im := by
    filter_upwards [hmem, hnear] with z hz hnearz
    by_cases him : 0 < z.im
    · rw [halfPlaneContinuousExtension_interior hupper hΦimage e he him]
      apply hupper
      rw [← hΦimage]
      exact ⟨z, him, rfl⟩
    · have hnonneg : 0 ≤ z.im := hz.1
      have him0 : z.im = 0 := le_antisymm (le_of_not_gt him) hnonneg
      have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him0]
      have hzball : z.re ∈ ball x ρ := by
        have hd : ‖z - (x : ℂ)‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hnearz
        have h := (Complex.abs_re_le_norm (z - (x : ℂ))).trans_lt hd
        simpa [mem_ball, Real.dist_eq] using h
      have hne : (halfPlaneContinuousExtension e z).im ≠ 0 := by
        intro hzero
        have hzero' : (halfPlaneContinuousExtension e (z.re : ℂ)).im = 0 := by
          rw [← hzreal]
          exact hzero
        have hxr := hisol z.re hzball hzero'
        have hzeq : z = (x : ℂ) := by rw [hzreal, hxr]
        exact hz.2 (by simpa [hzeq])
      obtain ⟨u, hu⟩ := halfPlaneContinuousExtension_boundary hΦimage e he he1 him0
      have hnonneg : 0 ≤ (halfPlaneContinuousExtension e z).im := by
        rw [hu]
        simpa [graphMap] using pastedFareyHeight_nonneg levels u
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  let T : ℂ → UpperHalfPlane := fun z =>
    if hz : 0 < (halfPlaneContinuousExtension e z).im then
      ⟨halfPlaneContinuousExtension e z, hz⟩ else ⟨Complex.I, by simp⟩
  have hTeq : (fun z => (T z : ℂ)) =ᶠ[L] halfPlaneContinuousExtension e := by
    filter_upwards [hpos] with z hz
    simp [T, hz]
  have hcont : ContinuousWithinAt (halfPlaneContinuousExtension e) C (x : ℂ) :=
    (halfPlaneContinuousExtension_continuousOn e he1) (x : ℂ) (by simp [C])
  have hbarlim : Tendsto (halfPlaneContinuousExtension e) L (𝓝 (r : ℂ)) := by
    have hle : L ≤ 𝓝[C] (x : ℂ) :=
      nhdsWithin_mono _ (show C \ {(x : ℂ)} ⊆ C from sdiff_subset)
    have h := hcont.tendsto.mono_left hle
    simpa only [hrval] using h
  have hTlim : Tendsto (fun z => (T z : ℂ)) L (𝓝 (r : ℂ)) := hbarlim.congr' hTeq.symm
  have hdom : ∀ᶠ z in L, pastedFareyHeight levels (T z : ℂ).re ≤ (T z : ℂ).im := by
    filter_upwards [hmem, hpos] with z hz hposz
    have hTz : (T z : ℂ) = halfPlaneContinuousExtension e z := by simp [T, hposz]
    rw [hTz]
    by_cases him : 0 < z.im
    · rw [halfPlaneContinuousExtension_interior hupper hΦimage e he him]
      have hΩ : Φ z ∈ upperGraphDomain (pastedFareyHeight levels) := by
        rw [← hΦimage]
        exact ⟨z, him, rfl⟩
      exact hΩ.le
    · have hnonneg : 0 ≤ z.im := hz.1
      have him0 : z.im = 0 := le_antisymm (le_of_not_gt him) hnonneg
      obtain ⟨u, hu⟩ := halfPlaneContinuousExtension_boundary hΦimage e he he1 him0
      rw [hu]
      simp [graphMap]
  have hheight := farey_vertex_inverse_height_closed_tendsto levels r hr0 γ p q hq hr h00 h10 T hTlim hdom
  have hlim := modularLambdaH_normalized_cusp_limit_of_formula (α := ℂ) (l := L) γ k hk
    (fun z => γ⁻¹ • T z) hheight
  have hcomposite :
      (fun z => cuspNormalize k (modularLambdaH ((γ • (γ⁻¹ • T z) : UpperHalfPlane) : ℂ))) =ᶠ[L]
        (fun z => cuspNormalize k (modularLambdaH (halfPlaneContinuousExtension e z))) := by
    filter_upwards [hpos] with z hz
    simp [T, hz]
  exact hlim.congr' hcomposite

theorem farey_normalized_cusp_limit_closed {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ)
    (hxvertex : (halfPlaneContinuousExtension e (x : ℂ)).im = 0) :
    ∃ k : Fin 6, Tendsto (fun z => cuspNormalize k
      (modularLambdaH (halfPlaneContinuousExtension e z)))
      (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ)) (𝓝 0) := by
  obtain ⟨r, hrgraph⟩ := halfPlaneContinuousExtension_boundary hΦimage e he he1 (z := (x : ℂ)) (by simp)
  have hr0 : pastedFareyHeight levels r = 0 := by
    rw [hrgraph] at hxvertex
    simpa [graphMap] using hxvertex
  have hrval : halfPlaneContinuousExtension e (x : ℂ) = (r : ℂ) := by
    rw [hrgraph]
    apply Complex.ext <;> simp [graphMap, hr0]
  obtain ⟨γ, p, q, hq, hr, h00, h10⟩ := pastedFarey_vertex_has_modular_matrix levels r hr0
  obtain ⟨k, hk⟩ := modularLambdaH_six_transforms γ
  exact ⟨k, farey_normalized_cusp_limit_closed_of_matrix hupper hΦimage e he he1 x r hr0 hrval
    γ p q hq hr h00 h10 k hk⟩

end ThreeOmittedValues
