module

public import Theorem12Proof.CuspRemovableGerm
public import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Tactic

/-!
# Meromorphic germs obtained from normalized cusp limits

The normalizations `z`, `1 - z`, and `1 / z` are involutions. Removing the
normalized singularity therefore gives a meromorphic normal-form germ for the
original function, with real value at the puncture.
-/

@[expose] public section

open Complex Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem cuspNormalize_involutive (k : Fin 6) (z : ℂ) :
    cuspNormalize k (cuspNormalize k z) = z := by
  fin_cases k <;> simp [cuspNormalize]

theorem cusp_normalization_has_meromorphic_germ {F : ℂ → ℂ} {x : ℂ} (k : Fin 6)
    {r : ℝ} (hr : 0 < r) (hF : DifferentiableOn ℂ F (ball x r \ {x}))
    (hzero : ∀ z ∈ ball x r \ {x}, F z ≠ 0)
    (hlim : Tendsto (fun z => cuspNormalize k (F z)) (𝓝[≠] x) (𝓝 0)) :
    ∃ G : ℂ → ℂ, MeromorphicNFAt G x ∧ (G x = 0 ∨ G x = 1) ∧
      G =ᶠ[𝓝[≠] x] F := by
  obtain ⟨g, hg, hgzero, hgeq⟩ := cusp_normalization_has_analytic_germ k hr hF hzero hlim
  let G : ℂ → ℂ := fun z => cuspNormalize k (g z)
  have hG : MeromorphicNFAt G x := by
    fin_cases k <;> simp only [G, cuspNormalize, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue]
    · exact hg.meromorphicNFAt
    · exact ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) x).sub hg).meromorphicNFAt
    · exact hg.meromorphicNFAt
    · exact ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) x).sub hg).meromorphicNFAt
    · exact hg.meromorphicNFAt.inv
    · exact hg.meromorphicNFAt.inv
  have hval : G x = 0 ∨ G x = 1 := by
    fin_cases k <;> simp [G, cuspNormalize, hgzero]
  refine ⟨G, hG, hval, ?_⟩
  filter_upwards [hgeq] with z hz
  change cuspNormalize k (g z) = F z
  rw [hz, cuspNormalize_involutive]

end ThreeOmittedValues
