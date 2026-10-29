module

public import Theorem12Proof.FareyBoundaryValues
public import Theorem12Proof.FareyBoundaryReal
public import Theorem12Proof.NoWanderingDomains.Hyperbolic.DiskModel.SchwarzReflection
import Mathlib.Tactic

/-!
# Schwarz reflection across nonvertex boundary points

At every real boundary point whose image lies in the upper half-plane,
the modular composite extends holomorphically across the real line.
The isolated vertices remain a separate problem.
-/

@[expose] public section

open Complex Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

noncomputable def fareyReflectedComposite {levels : ℤ → ℕ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels))) : ℂ → ℂ :=
  schwarzReflect (fun z => modularLambdaH (halfPlaneContinuousExtension e z))

theorem exists_positive_extension_ball {Ω : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ closure (halfPlaneToCayley '' Ω))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ)
    (hx : 0 < (halfPlaneContinuousExtension e (x : ℂ)).im) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ ball (x : ℂ) r, 0 ≤ z.im →
      0 < (halfPlaneContinuousExtension e z).im := by
  let C : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let H : Set ℂ := {z : ℂ | 0 < z.im}
  have hcont : ContinuousWithinAt (halfPlaneContinuousExtension e) C (x : ℂ) :=
    (halfPlaneContinuousExtension_continuousOn e he1) (x : ℂ) (by simp [C])
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hev : {z : ℂ | halfPlaneContinuousExtension e z ∈ H} ∈ 𝓝[C] (x : ℂ) :=
    hcont.tendsto (hH.mem_nhds hx)
  obtain ⟨U, hU, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r, hr, ?_⟩
  intro z hz hzim
  exact hsub ⟨hrsub hz, hzim⟩

theorem farey_reflection_at_open_edge {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hupper : upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im})
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ)
    (hx : 0 < (halfPlaneContinuousExtension e (x : ℂ)).im) :
    ∃ r : ℝ, 0 < r ∧ DifferentiableOn ℂ (fareyReflectedComposite e) (ball (x : ℂ) r) ∧
      ∀ z ∈ ball (x : ℂ) r, 0 < z.im →
        fareyReflectedComposite e z = modularLambdaH (Φ z) := by
  obtain ⟨r, hr, hball⟩ := exists_positive_extension_ball e he1 x hx
  let C : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let H : Set ℂ := {z : ℂ | 0 < z.im}
  let B : Set ℂ := ball (x : ℂ) r
  let f : ℂ → ℂ := fun z => modularLambdaH (halfPlaneContinuousExtension e z)
  have hmaps : MapsTo (halfPlaneContinuousExtension e) (B ∩ C) H := by
    intro z hz
    exact hball z hz.1 hz.2
  have hfcont : ContinuousOn f (B ∩ C) := by
    exact modularLambdaH_differentiableOn.continuousOn.comp
      ((halfPlaneContinuousExtension_continuousOn e he1).mono inter_subset_right) hmaps
  have hΦmaps : MapsTo Φ H H := by
    intro z hz
    apply hupper
    rw [← hΦimage]
    exact ⟨z, hz, rfl⟩
  have hfbase : DifferentiableOn ℂ (fun z => modularLambdaH (Φ z)) H :=
    modularLambdaH_differentiableOn.comp hΦ hΦmaps
  have hfdiff : DifferentiableOn ℂ f (B ∩ H) := by
    apply (hfbase.mono inter_subset_right).congr
    intro z hz
    dsimp [f]
    rw [halfPlaneContinuousExtension_interior hupper hΦimage e he hz.2]
  have hfreal : ∀ z ∈ B, z.im = 0 → (f z).im = 0 := by
    intro z hz hz0
    have hzpos : 0 < (halfPlaneContinuousExtension e z).im := hball z hz (by linarith)
    obtain ⟨u, hu⟩ := halfPlaneContinuousExtension_boundary hΦimage e he he1 hz0
    have hgraph : halfPlaneContinuousExtension e z ∈ globalFareyArcs levels := by
      rw [globalFareyArcs_eq_graph]
      rw [hu]
      simp [graphMap]
    exact modularLambdaH_real_on_globalFareyArcs levels hgraph hzpos
  have hsym : IsRealSymmetric B := by
    intro z hz
    change dist ((starRingEnd ℂ) z) (x : ℂ) < r
    have hdist := Complex.dist_conj_conj z (x : ℂ)
    simpa using hdist.trans_lt hz
  have hreflect : DifferentiableOn ℂ (schwarzReflect f) B :=
    schwarzReflect_differentiableOn isOpen_ball hsym hfcont hfdiff hfreal
  refine ⟨r, hr, hreflect, ?_⟩
  intro z _hz hzim
  rw [fareyReflectedComposite, schwarzReflect_apply_of_im_nonneg _ hzim.le]
  exact congrArg modularLambdaH (halfPlaneContinuousExtension_interior hupper hΦimage e he hzim)

end ThreeOmittedValues
