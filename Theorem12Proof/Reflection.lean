module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Reflection of Blaschke sums

This file isolates the arithmetic of the reflection used in the lower
half-plane part of Theorem 1.2 of arXiv:2608.26062v2. A multiplicity function
is kept explicit; the identification of reflected meromorphic divisors is
a separate obligation.
-/

@[expose] public section

namespace ThreeOmittedValues

/-- The weight in the half-plane Blaschke condition. -/
noncomputable def blaschkeWeight (z : ℂ) : ℝ :=
  |z.im| / (1 + ‖z‖ ^ 2)

/-- Complex conjugation leaves the half-plane Blaschke weight unchanged. -/
theorem blaschkeWeight_conj (z : ℂ) :
    blaschkeWeight ((starRingEnd ℂ) z) = blaschkeWeight z := by
  simp [blaschkeWeight]

/-- Weighted multiplicities restricted to the upper half-plane. -/
noncomputable def upperBlaschkeTerms (mult : ℂ → ℕ) (z : ℂ) : ℝ :=
  if 0 < z.im then (mult z : ℝ) * blaschkeWeight z else 0

/-- Weighted multiplicities restricted to the lower half-plane. -/
noncomputable def lowerBlaschkeTerms (mult : ℂ → ℕ) (z : ℂ) : ℝ :=
  if z.im < 0 then (mult z : ℝ) * blaschkeWeight z else 0

/-- A divisor reflected across the real axis has the same summand at the
corresponding conjugate point. -/
theorem lowerBlaschkeTerms_conj (mult : ℂ → ℕ) (z : ℂ) :
    lowerBlaschkeTerms (fun w => mult ((starRingEnd ℂ) w)) ((starRingEnd ℂ) z) =
      upperBlaschkeTerms mult z := by
  simp [lowerBlaschkeTerms, upperBlaschkeTerms, blaschkeWeight_conj]

/-- Conjugation preserves the convergence, and hence the divergence, of the
weighted sum when the multiplicities are reflected along with the points. -/
theorem summable_lower_reflected_iff (mult : ℂ → ℕ) :
    Summable (lowerBlaschkeTerms (fun w => mult ((starRingEnd ℂ) w))) ↔
      Summable (upperBlaschkeTerms mult) := by
  have h := (Complex.conjCLE.toEquiv).summable_iff
    (f := lowerBlaschkeTerms (fun w => mult ((starRingEnd ℂ) w)))
  change (Summable fun z => lowerBlaschkeTerms
      (fun w => mult ((starRingEnd ℂ) w)) ((starRingEnd ℂ) z)) ↔ _ at h
  simpa only [lowerBlaschkeTerms_conj] using h.symm

end ThreeOmittedValues
