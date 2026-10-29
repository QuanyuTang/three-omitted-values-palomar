module

public import Theorem12Proof.FareyCompactVariation
public import Theorem12Proof.FareyCompactEmbedding
public import Theorem12Proof.ClosedRealCurveInjective
public import Theorem12Proof.RectifiablePeriodic
import Mathlib.Tactic

/-!
# The compactified Farey graph is a rectifiable Jordan curve

This proves the geometric curve itself is rectifiable and simple. Identifying
it with the frontier of the compactified upper graph domain remains separate.
-/

@[expose] public section

open Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

noncomputable def compactFareyCurve (levels : ℤ → ℕ) : ℝ → ℂ :=
  closeRealCurve (halfPlaneToCayley ∘ graphMap (pastedFareyHeight levels)) 1

theorem compactFareyCurve_properties (levels : ℤ → ℕ) :
    ContinuousOn (compactFareyCurve levels) (Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    BoundedVariationOn (compactFareyCurve levels) (Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    compactFareyCurve levels (-(Real.pi / 2)) = compactFareyCurve levels (Real.pi / 2) ∧
    InjOn (compactFareyCurve levels) (Ico (-(Real.pi / 2)) (Real.pi / 2)) ∧
    compactFareyCurve levels '' Icc (-(Real.pi / 2)) (Real.pi / 2) =
      insert 1 (Set.range (halfPlaneToCayley ∘ graphMap (pastedFareyHeight levels))) := by
  have hGcont : Continuous (halfPlaneToCayley ∘ graphMap (pastedFareyHeight levels)) :=
    compactGraph_continuous (pastedFareyHeight_continuous levels) (pastedFareyHeight_nonneg levels)
  have hbot := compactFareyGraph_tendsto_one_atBot levels
  have htop := compactFareyGraph_tendsto_one_atTop levels
  refine ⟨closeRealCurve_continuousOn hGcont hbot htop,
    closeRealCurve_boundedVariation (compactFareyGraph_boundedVariation levels) hbot htop,
    ?_, closeRealCurve_injOn (compactGraph_injective (pastedFareyHeight_nonneg levels))
      (compactGraph_ne_one (pastedFareyHeight_nonneg levels)),
    closeRealCurve_image _ _⟩
  simp [compactFareyCurve]

/-- A globally Lipschitz periodic Jordan parametrization of the exact
compactified Farey graph. -/
theorem exists_periodic_lipschitz_compactFareyGraph (levels : ℤ → ℕ) :
    ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * Real.pi) ∧
      InjOn γ (Ico 0 (2 * Real.pi)) ∧
      γ '' Icc 0 (2 * Real.pi) =
        insert 1 (Set.range (halfPlaneToCayley ∘ graphMap (pastedFareyHeight levels))) := by
  have hab : -(Real.pi / 2) < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨hcont, hvar, hclosed, hinj, himage⟩ := compactFareyCurve_properties levels
  obtain ⟨γ, hLip, hper, hγinj, hγimage⟩ :=
    exists_periodic_lipschitz_of_rectifiable hab hvar hcont hclosed hinj
  exact ⟨γ, hLip, hper, hγinj, hγimage.trans himage⟩

end ThreeOmittedValues
