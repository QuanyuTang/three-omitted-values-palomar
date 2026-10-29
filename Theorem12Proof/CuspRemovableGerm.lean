module

public import Theorem12Proof.ModularCuspLimits
public import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic

/-!
# Removing a normalized cusp singularity

If a reflected function is holomorphic and omits zero on a punctured disk,
and a cusp normalization tends to zero, that normalization extends
holomorphically across the center with value zero.
-/

@[expose] public section

open Complex Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem cusp_normalization_has_analytic_germ {F : ℂ → ℂ} {x : ℂ} (k : Fin 6)
    {r : ℝ} (hr : 0 < r) (hF : DifferentiableOn ℂ F (ball x r \ {x}))
    (hzero : ∀ z ∈ ball x r \ {x}, F z ≠ 0)
    (hlim : Tendsto (fun z => cuspNormalize k (F z)) (𝓝[≠] x) (𝓝 0)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x = 0 ∧
      ∀ᶠ z in 𝓝[≠] x, g z = cuspNormalize k (F z) := by
  let N : ℂ → ℂ := fun z => cuspNormalize k (F z)
  let g : ℂ → ℂ := Function.update N x 0
  have hN : DifferentiableOn ℂ N (ball x r \ {x}) := by
    fin_cases k <;> simp only [N, cuspNormalize, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue]
    · exact hF
    · exact hF.const_sub 1
    · exact hF
    · exact hF.const_sub 1
    · exact hF.inv hzero
    · exact hF.inv hzero
  have hgDiff : DifferentiableOn ℂ g (ball x r \ {x}) := by
    apply hN.congr
    intro z hz
    have hne : z ≠ x := by simpa using hz.2
    simp [g, Function.update_of_ne hne]
  have hgCont : ContinuousAt g x := by
    apply continuousAt_update_same.mpr
    exact hlim
  have hgOn : DifferentiableOn ℂ g (ball x r) :=
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds x hr)).mp
      ⟨hgDiff, hgCont⟩
  have hgan : AnalyticAt ℂ g x := (hgOn.analyticOnNhd isOpen_ball) x (mem_ball_self hr)
  refine ⟨g, hgan, by simp [g], ?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with z hz
  have hne : z ≠ x := by simpa using hz
  simp [g, N, Function.update_of_ne hne]

end ThreeOmittedValues
