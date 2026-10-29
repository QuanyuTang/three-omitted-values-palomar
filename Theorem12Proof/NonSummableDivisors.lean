module

public import Theorem12Proof.OrbitDivisors
import Mathlib.Tactic

/-!
# Divergent point families give divergent divisors

This form accepts any injective family whose Blaschke weights are already
known not to be summable, including the concrete families constructed above.
-/

@[expose] public section

namespace ThreeOmittedValues

theorem not_upperBlaschke_of_nonsummable_points {ι : Type*} {f : ℂ → ℂ} {a b w : ℂ}
    (hf : MeromorphicOn f Set.univ) (hw : w ∈ finiteValueFiber f b) (hba : b ≠ a)
    (p : ι → ℂ) (hp_inj : Function.Injective p)
    (hp_fibre : ∀ i, p i ∈ finiteValueFiber f a)
    (hp_upper : ∀ i, 0 < (p i).im)
    (hdiv : ¬ Summable (fun i => blaschkeWeight (p i))) :
    ¬ upperBlaschkeCondition f a := by
  have hnonneg (i : ι) : 0 ≤ blaschkeWeight (p i) :=
    div_nonneg (abs_nonneg _) (by positivity)
  intro hblaschke
  have hcomp : Summable (fun i : ι => upperBlaschkeTerms (aPointMultiplicity f a) (p i)) :=
    hblaschke.comp_injective hp_inj
  apply hdiv
  apply hcomp.of_nonneg_of_le hnonneg
  intro i
  have hmult : (1 : ℝ) ≤ aPointMultiplicity f a (p i) := by
    exact_mod_cast aPointMultiplicity_pos_of_distinct_value hf hw hba (hp_fibre i)
  have hle := mul_le_mul_of_nonneg_right hmult (hnonneg i)
  simpa [upperBlaschkeTerms, hp_upper i] using hle

theorem not_lowerBlaschke_of_reflected_nonsummable_points {ι : Type*} {f : ℂ → ℂ} {a b w : ℂ}
    (hf : MeromorphicOn f Set.univ) (hw : w ∈ finiteValueFiber f b) (hba : b ≠ a)
    (hsym : ∀ u, f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (f u))
    (p : ι → ℂ) (hp_inj : Function.Injective p)
    (hp_fibre : ∀ i, p i ∈ finiteValueFiber f ((starRingEnd ℂ) a))
    (hp_upper : ∀ i, 0 < (p i).im)
    (hdiv : ¬ Summable (fun i => blaschkeWeight (p i))) :
    ¬ lowerBlaschkeCondition f a := by
  have hnonneg (i : ι) : 0 ≤ blaschkeWeight (p i) :=
    div_nonneg (abs_nonneg _) (by positivity)
  have hinj : Function.Injective (fun i => (starRingEnd ℂ) (p i)) := by
    intro i j hij
    apply hp_inj
    have h := congrArg (starRingEnd ℂ) hij
    simpa only [Complex.conj_conj] using h
  intro hblaschke
  have hcomp : Summable (fun i : ι =>
      lowerBlaschkeTerms (aPointMultiplicity f a) ((starRingEnd ℂ) (p i))) :=
    hblaschke.comp_injective hinj
  apply hdiv
  apply hcomp.of_nonneg_of_le hnonneg
  intro i
  have hfinite : (starRingEnd ℂ) (p i) ∈ finiteValueFiber f a := by
    have h := finiteValueFiber_conj_of_realSymmetric hsym (hp_fibre i)
    simpa only [Complex.conj_conj] using h
  have hmult : (1 : ℝ) ≤ aPointMultiplicity f a ((starRingEnd ℂ) (p i)) := by
    exact_mod_cast aPointMultiplicity_pos_of_distinct_value hf hw hba hfinite
  have hle := mul_le_mul_of_nonneg_right hmult (hnonneg i)
  have him : ((starRingEnd ℂ) (p i)).im < 0 := by
    simpa using neg_neg_of_pos (hp_upper i)
  simpa [lowerBlaschkeTerms, him, hp_upper i, blaschkeWeight_conj] using hle

end ThreeOmittedValues
