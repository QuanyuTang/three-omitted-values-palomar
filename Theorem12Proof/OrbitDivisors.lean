module

public import Theorem12Proof.TotientDivergence
public import Theorem12Proof.DivisorPositivity
public import Theorem12Proof.AnalyticReflection
import Mathlib.Tactic

/-!
# From a divergent family of points to a divergent divisor

This abstract reduction connects the explicit arithmetic index family to
the actual meromorphic divisor. The geometric estimates and the application
to the constructed function appear in the later orbit and main modules.
-/

@[expose] public section

namespace ThreeOmittedValues

/-- An injective family of analytic `a`-points in the upper half-plane,
with the indicated eventual lower bound on their actual Blaschke weights,
forces the `a`-divisor to fail the Blaschke condition. -/
theorem not_upperBlaschke_of_orbit_points {f : ℂ → ℂ} {a b w : ℂ}
    (hf : MeromorphicOn f Set.univ) (hw : w ∈ finiteValueFiber f b) (hba : b ≠ a)
    (p : OrbitIndex → ℂ) (hp_inj : Function.Injective p)
    (hp_fibre : ∀ i, p i ∈ finiteValueFiber f a)
    (hp_upper : ∀ i, 0 < (p i).im) {c : ℝ} (hc : 0 < c)
    (hp_weight : ∃ M : ℕ, ∀ m ≥ M, ∀ d : {d // d ∈ orbitIndices m},
      c / ((m : ℝ) ^ 2 * Real.log (m : ℝ)) ≤ blaschkeWeight (p ⟨m, d⟩)) :
    ¬ upperBlaschkeCondition f a := by
  let W : OrbitIndex → ℝ := fun i => upperBlaschkeTerms (aPointMultiplicity f a) (p i)
  have hW_nonneg (i : OrbitIndex) : 0 ≤ W i := by
    dsimp [W, upperBlaschkeTerms]
    simp only [hp_upper i, ite_true]
    exact mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (abs_nonneg _) (by positivity))
  have hW_bound : ∃ M : ℕ, ∀ m ≥ M, ∀ d : {d // d ∈ orbitIndices m},
      c / ((m : ℝ) ^ 2 * Real.log (m : ℝ)) ≤ W ⟨m, d⟩ := by
    obtain ⟨M, hM⟩ := hp_weight
    refine ⟨M, ?_⟩
    intro m hm d
    let i : OrbitIndex := ⟨m, d⟩
    have hmult : (1 : ℝ) ≤ aPointMultiplicity f a (p i) := by
      exact_mod_cast aPointMultiplicity_pos_of_distinct_value hf hw hba (hp_fibre i)
    have hweight : 0 ≤ blaschkeWeight (p i) :=
      div_nonneg (abs_nonneg _) (by positivity)
    have hle := mul_le_mul_of_nonneg_right hmult hweight
    have hle' : blaschkeWeight (p i) ≤ W i := by
      simpa [W, upperBlaschkeTerms, hp_upper i] using hle
    exact (hM m hm d).trans hle'
  have hdiv : ¬ Summable W := not_summable_of_orbit_lower_bound W hW_nonneg hc hW_bound
  intro hblaschke
  apply hdiv
  exact hblaschke.comp_injective hp_inj

/-- Tail-indexed version matching the article: points at finitely many
earlier levels are not required to exist in the domain. -/
theorem not_upperBlaschke_of_orbit_tail_points {f : ℂ → ℂ} {a b w : ℂ}
    (hf : MeromorphicOn f Set.univ) (hw : w ∈ finiteValueFiber f b) (hba : b ≠ a)
    (N : ℕ) (p : OrbitIndexFrom N → ℂ) (hp_inj : Function.Injective p)
    (hp_fibre : ∀ i, p i ∈ finiteValueFiber f a)
    (hp_upper : ∀ i, 0 < (p i).im) {c : ℝ} (hc : 0 < c)
    (hp_weight : ∀ m : {m : ℕ // N ≤ m}, ∀ d : {d // d ∈ orbitIndices m.1},
      c / ((m.1 : ℝ) ^ 2 * Real.log (m.1 : ℝ)) ≤ blaschkeWeight (p ⟨m, d⟩)) :
    ¬ upperBlaschkeCondition f a := by
  have hnonneg (i : OrbitIndexFrom N) : 0 ≤ blaschkeWeight (p i) :=
    div_nonneg (abs_nonneg _) (by positivity)
  have hdiv : ¬ Summable (fun i : OrbitIndexFrom N => blaschkeWeight (p i)) :=
    not_summable_of_orbit_tail_lower_bound N _ hnonneg hc hp_weight
  intro hblaschke
  have hcomp : Summable (fun i : OrbitIndexFrom N =>
      upperBlaschkeTerms (aPointMultiplicity f a) (p i)) :=
    hblaschke.comp_injective hp_inj
  apply hdiv
  apply hcomp.of_nonneg_of_le hnonneg
  intro i
  have hmult : (1 : ℝ) ≤ aPointMultiplicity f a (p i) := by
    exact_mod_cast aPointMultiplicity_pos_of_distinct_value hf hw hba (hp_fibre i)
  have hle := mul_le_mul_of_nonneg_right hmult (hnonneg i)
  simpa [upperBlaschkeTerms, hp_upper i] using hle

/-- Reflect an upper-half-plane orbit family of `conj a`-points to obtain
a divergent `a`-divisor in the lower half-plane. No equality of the full
reflected divisors is assumed. -/
theorem not_lowerBlaschke_of_reflected_orbit_tail_points {f : ℂ → ℂ} {a b w : ℂ}
    (hf : MeromorphicOn f Set.univ) (hw : w ∈ finiteValueFiber f b) (hba : b ≠ a)
    (hsym : ∀ u, f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (f u))
    (N : ℕ) (p : OrbitIndexFrom N → ℂ) (hp_inj : Function.Injective p)
    (hp_fibre : ∀ i, p i ∈ finiteValueFiber f ((starRingEnd ℂ) a))
    (hp_upper : ∀ i, 0 < (p i).im) {c : ℝ} (hc : 0 < c)
    (hp_weight : ∀ m : {m : ℕ // N ≤ m}, ∀ d : {d // d ∈ orbitIndices m.1},
      c / ((m.1 : ℝ) ^ 2 * Real.log (m.1 : ℝ)) ≤ blaschkeWeight (p ⟨m, d⟩)) :
    ¬ lowerBlaschkeCondition f a := by
  have hnonneg (i : OrbitIndexFrom N) : 0 ≤ blaschkeWeight (p i) :=
    div_nonneg (abs_nonneg _) (by positivity)
  have hdiv : ¬ Summable (fun i : OrbitIndexFrom N => blaschkeWeight (p i)) :=
    not_summable_of_orbit_tail_lower_bound N _ hnonneg hc hp_weight
  have hinj : Function.Injective (fun i => (starRingEnd ℂ) (p i)) := by
    intro i j hij
    apply hp_inj
    have h := congrArg (starRingEnd ℂ) hij
    simpa only [Complex.conj_conj] using h
  intro hblaschke
  have hcomp : Summable (fun i : OrbitIndexFrom N =>
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
