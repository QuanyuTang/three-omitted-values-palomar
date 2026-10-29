module

public import Theorem12Proof.DivisorSums
import Mathlib.Tactic

/-!
# Positivity of finite-value multiplicities

These lemmas connect analytic fibres to the positive part of Mathlib's
meromorphic divisor, under an independently supplied distinct value.
-/

@[expose] public section

namespace ThreeOmittedValues

/-- An analytic `a`-point has positive multiplicity if the meromorphic
function takes a distinct finite value somewhere on the plane. -/
theorem aPointMultiplicity_pos_of_distinct_value {f : ℂ → ℂ} {a b w z : ℂ}
    (hf : MeromorphicOn f Set.univ) (hw : w ∈ finiteValueFiber f b) (hba : b ≠ a)
    (hz : z ∈ finiteValueFiber f a) : 0 < aPointMultiplicity f a z := by
  let g : ℂ → ℂ := fun t => f t - a
  have hga : AnalyticAt ℂ g z := hz.1.sub analyticAt_const
  have hgzero : g z = 0 := by simp [g, hz.2]
  have hgtop : meromorphicOrderAt g z ≠ ⊤ :=
    aPoint_order_ne_top_of_distinct_value hf hw hba
  have hg0 : 0 ≤ meromorphicOrderAt g z := hga.meromorphicOrderAt_nonneg
  have hgne : meromorphicOrderAt g z ≠ 0 := by
    intro h
    have : g z ≠ 0 := hga.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h
    exact this hgzero
  have hgpos : 0 < meromorphicOrderAt g z := lt_of_le_of_ne hg0 hgne.symm
  have hco := WithTop.coe_untop₀_of_ne_top hgtop
  have hgpos' : 0 < (meromorphicOrderAt g z).untop₀ := by
    have h : (0 : WithTop ℤ) < ((meromorphicOrderAt g z).untop₀ : WithTop ℤ) := by
      rw [hco]
      exact hgpos
    exact WithTop.coe_lt_coe.mp h
  have hgmer : MeromorphicOn g Set.univ := by
    intro t ht
    exact (hf t ht).sub analyticAt_const.meromorphicAt
  have hnat : (((meromorphicOrderAt g z).untop₀.toNat : ℕ) : ℤ) =
      (meromorphicOrderAt g z).untop₀ := Int.toNat_of_nonneg hgpos'.le
  rw [aPointMultiplicity, MeromorphicOn.divisor_apply hgmer (Set.mem_univ z)]
  omega

end ThreeOmittedValues
