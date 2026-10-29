module

public import Theorem12Proof.CurveReparametrization
public import Theorem12Proof.Vendor.PeriodicJordan

/-!
# Periodic Lipschitz parametrization of a rectifiable Jordan loop

The hypothesis is an actual bounded-variation Jordan parametrization; this
does not assert that the Farey boundary satisfies it.
-/

@[expose] public section
open Set

namespace ThreeOmittedValues

/-- Reparametrize a continuous rectifiable Jordan loop by a Lipschitz
`2π`-periodic curve without changing its image. -/
theorem exists_periodic_lipschitz_of_rectifiable {c : ℝ → ℂ} {a b : ℝ}
    (hab : a < b) (hvar : BoundedVariationOn c (Icc a b))
    (hcont : ContinuousOn c (Icc a b)) (hclosed : c a = c b)
    (hinj : InjOn c (Ico a b)) :
    ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * Real.pi) ∧
      InjOn γ (Ico 0 (2 * Real.pi)) ∧ γ '' Icc 0 (2 * Real.pi) = c '' Icc a b := by
  obtain ⟨Γ, hΓ, T, hT, hclosedΓ, hinjΓ, himageΓ⟩ :=
    exists_lipschitz_loop_of_rectifiable hab hvar hcont hclosed hinj
  obtain ⟨γ, hγ, hper, hγinj, hγimage⟩ :=
    exists_periodic_of_loop hΓ hT hclosedΓ hinjΓ
  exact ⟨γ, hγ, hper, hγinj, hγimage.trans himageΓ⟩

end ThreeOmittedValues
