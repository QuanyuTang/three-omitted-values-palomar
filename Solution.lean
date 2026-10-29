module

public import Theorem12Proof.Theorem12Research

@[expose] public section

namespace PalomarTheorem12

open ThreeOmittedValues

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
  exact theorem_1_2

end PalomarTheorem12
