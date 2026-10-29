module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Theorem 1.2: Three omitted values and non-Blaschke point divisors

This is the statement surface for arXiv:2608.26062v2, Theorem 1.2. A
finite fibre requires analyticity because Mathlib's complex-valued normal
form assigns the default value zero at a pole. The positive part of the
meromorphic divisor counts the multiplicity of each finite point.
-/

@[expose] public section

noncomputable section

namespace ThreeOmittedValues

/- Match the canonical complex scalar instance used by the fibre definitions
   in the proof modules. The instances are definitionally equivalent. -/
section

attribute [local instance 10000] NormedField.toNormedSpace

/-- Points where the meromorphic function takes the finite value `a`. -/
def finiteValueFiber (f : ℂ → ℂ) (a : ℂ) : Set ℂ :=
  {z | AnalyticAt ℂ f z ∧ f z = a}

/-- Poles of a function that is meromorphic in normal form on the plane. -/
def poleFiber (f : ℂ → ℂ) : Set ℂ :=
  {z | ¬ AnalyticAt ℂ f z}

end

/-- The standard half-plane Blaschke weight. -/
def blaschkeWeight (z : ℂ) : ℝ :=
  |z.im| / (1 + ‖z‖ ^ 2)

/-- Weighted multiplicities in the upper half-plane. -/
def upperBlaschkeTerms (mult : ℂ → ℕ) (z : ℂ) : ℝ :=
  if 0 < z.im then (mult z : ℝ) * blaschkeWeight z else 0

/-- Weighted multiplicities in the lower half-plane. -/
def lowerBlaschkeTerms (mult : ℂ → ℕ) (z : ℂ) : ℝ :=
  if z.im < 0 then (mult z : ℝ) * blaschkeWeight z else 0

section

attribute [local instance 10000] NormedField.toNormedSpace

/-- Multiplicity of the finite `a`-point, the positive part of `divisor (f-a)`. -/
def aPointMultiplicity (f : ℂ → ℂ) (a z : ℂ) : ℕ :=
  (MeromorphicOn.divisor (fun w => f w - a) Set.univ z).toNat

end

/-- The finite `a`-point divisor satisfies the upper Blaschke condition. -/
def upperBlaschkeCondition (f : ℂ → ℂ) (a : ℂ) : Prop :=
  Summable (upperBlaschkeTerms (aPointMultiplicity f a))

/-- The finite `a`-point divisor satisfies the lower Blaschke condition. -/
def lowerBlaschkeCondition (f : ℂ → ℂ) (a : ℂ) : Prop :=
  Summable (lowerBlaschkeTerms (aPointMultiplicity f a))

/-- A quotient of bounded analytic functions on the upper half-plane. -/
def IsBoundedTypeOnUpper (F : ℂ → ℂ) : Prop :=
  ∃ (u v : ℂ → ℂ) (Cu Cv : ℝ),
    AnalyticOnNhd ℂ u {z : ℂ | 0 < z.im} ∧
    AnalyticOnNhd ℂ v {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 < z.im → ‖u z‖ ≤ Cu) ∧
    (∀ z : ℂ, 0 < z.im → ‖v z‖ ≤ Cv) ∧
    (∃ z : ℂ, 0 < z.im ∧ v z ≠ 0) ∧
    (∀ z : ℂ, 0 < z.im → v z ≠ 0 → F z = u z / v z)

/-- A quotient of bounded analytic functions on the lower half-plane. -/
def IsBoundedTypeOnLower (F : ℂ → ℂ) : Prop :=
  ∃ (u v : ℂ → ℂ) (Cu Cv : ℝ),
    AnalyticOnNhd ℂ u {z : ℂ | z.im < 0} ∧
    AnalyticOnNhd ℂ v {z : ℂ | z.im < 0} ∧
    (∀ z : ℂ, z.im < 0 → ‖u z‖ ≤ Cu) ∧
    (∀ z : ℂ, z.im < 0 → ‖v z‖ ≤ Cv) ∧
    (∃ z : ℂ, z.im < 0 ∧ v z ≠ 0) ∧
    (∀ z : ℂ, z.im < 0 → v z ≠ 0 → F z = u z / v z)

end ThreeOmittedValues

namespace PalomarTheorem12

open ThreeOmittedValues

/-- A real meromorphic function has infinite real fibres over 0, 1 and infinity,
and every other point divisor fails the Blaschke condition in both half-planes.
The function is not of bounded type in either half-plane. -/
theorem main_result :
  ∃ F : ℂ → ℂ,
    MeromorphicNFOn F Set.univ ∧
    (∀ z, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z)) ∧
    finiteValueFiber F 0 ⊆ {z : ℂ | z.im = 0} ∧
    finiteValueFiber F 1 ⊆ {z : ℂ | z.im = 0} ∧
    poleFiber F ⊆ {z : ℂ | z.im = 0} ∧
    (finiteValueFiber F 0).Infinite ∧
    (finiteValueFiber F 1).Infinite ∧
    (poleFiber F).Infinite ∧
    (∀ a : ℂ, a ≠ 0 → a ≠ 1 →
      ¬ upperBlaschkeCondition F a ∧ ¬ lowerBlaschkeCondition F a) ∧
    ¬ IsBoundedTypeOnUpper F ∧ ¬ IsBoundedTypeOnLower F := by
  sorry

end PalomarTheorem12

end
