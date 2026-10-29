module

public import Theorem12Proof.MeromorphicFibres
public import Theorem12Proof.Reflection

/-!
# Multiplicities and the half-plane Blaschke condition

For a nonconstant meromorphic function, the positive part of the divisor of
`f - a` records the orders of its `a`-points. The source theorem's hypotheses
on the special fibres force nonconstancy. Here the ambient sum ranges over all
of `ℂ`; points outside the relevant fibre have multiplicity zero.
-/

@[expose] public section

namespace ThreeOmittedValues

/-- Multiplicity of a finite `a`-point, as the positive part of Mathlib's
meromorphic divisor of `f - a`. -/
noncomputable def aPointMultiplicity (f : ℂ → ℂ) (a z : ℂ) : ℕ :=
  (MeromorphicOn.divisor (fun w => f w - a) Set.univ z).toNat

/-- The Blaschke summability condition for a finite-value divisor in the
upper half-plane. -/
def upperBlaschkeCondition (f : ℂ → ℂ) (a : ℂ) : Prop :=
  Summable (upperBlaschkeTerms (aPointMultiplicity f a))

/-- The corresponding condition in the lower half-plane. -/
def lowerBlaschkeCondition (f : ℂ → ℂ) (a : ℂ) : Prop :=
  Summable (lowerBlaschkeTerms (aPointMultiplicity f a))

/-- If a meromorphic function takes a finite value `b ≠ a` at some point,
then the order of `f - a` is finite everywhere on the connected plane. This
rules out Mathlib's infinite-order convention when interpreting the divisor. -/
theorem aPoint_order_ne_top_of_distinct_value {f : ℂ → ℂ} {a b w z : ℂ}
    (hf : MeromorphicOn f Set.univ) (hw : w ∈ finiteValueFiber f b) (hba : b ≠ a) :
    meromorphicOrderAt (fun t => f t - a) z ≠ ⊤ := by
  have hga : AnalyticAt ℂ (fun t => f t - a) w := hw.1.sub analyticAt_const
  have hne : (fun t => f t - a) w ≠ 0 := by simpa only [hw.2, sub_ne_zero] using hba
  have hzero : meromorphicOrderAt (fun t => f t - a) w = 0 :=
    hga.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hne
  have hg : MeromorphicOn (fun t => f t - a) Set.univ := by
    intro t ht
    exact (hf t ht).sub analyticAt_const.meromorphicAt
  have hex : ∃ u ∈ (Set.univ : Set ℂ), meromorphicOrderAt (fun t => f t - a) u ≠ ⊤ := by
    exact ⟨w, Set.mem_univ w, by rw [hzero]; simp⟩
  exact (hg.exists_meromorphicOrderAt_ne_top_iff_forall_mem isConnected_univ).mp hex z
    (Set.mem_univ z)

/-- A pole is not an `a`-point, even for `a = 0`. -/
theorem aPointMultiplicity_eq_zero_at_pole {f : ℂ → ℂ} {a z : ℂ}
    (hf : MeromorphicOn f Set.univ) (hz : meromorphicOrderAt f z < 0) :
    aPointMultiplicity f a z = 0 := by
  have hconst : AnalyticAt ℂ (fun _ : ℂ => -a) z := analyticAt_const
  have heq : meromorphicOrderAt (fun w => f w - a) z = meromorphicOrderAt f z := by
    have hfun : (fun w => f w - a) = f + (fun _ => -a) := by
      funext w
      simp only [Pi.add_apply, sub_eq_add_neg]
    rw [hfun]
    have h := meromorphicOrderAt_add_eq_left_of_lt hconst.meromorphicAt
      (lt_of_lt_of_le hz hconst.meromorphicOrderAt_nonneg)
    exact h
  have hfa : MeromorphicOn (fun w => f w - a) Set.univ := by
    intro w hw
    exact (hf w hw).sub analyticAt_const.meromorphicAt
  have hle : (meromorphicOrderAt f z).untop₀ ≤ 0 := by
    simpa using WithTop.untop₀_le_untop₀ (b := 0) (by simp) hz.le
  rw [aPointMultiplicity, MeromorphicOn.divisor_apply hfa (Set.mem_univ z), heq]
  exact Int.toNat_of_nonpos hle

end ThreeOmittedValues
