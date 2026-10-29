module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Complex.Basic

/-!
# Finite values and poles of meromorphic normal forms

Mathlib's complex-valued normal form takes the value `0` at poles. Consequently,
a finite value fibre must also require analyticity at the point; plain
pointwise equality would incorrectly include poles in the zero fibre.
-/

@[expose] public section

namespace ThreeOmittedValues

/-- The fibre of a finite value for a complex-valued meromorphic normal form. -/
def finiteValueFiber (f : ℂ → ℂ) (a : ℂ) : Set ℂ :=
  {z | AnalyticAt ℂ f z ∧ f z = a}

/-- The pole fibre on a domain where the function is meromorphic. -/
def poleFiber (f : ℂ → ℂ) : Set ℂ :=
  {z | ¬ AnalyticAt ℂ f z}

/-- A normal-form meromorphic function has a pole exactly at the points of
strictly negative meromorphic order. -/
theorem mem_poleFiber_iff_order_lt_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicNFAt f z) :
    z ∈ poleFiber f ↔ meromorphicOrderAt f z < 0 := by
  change (¬ AnalyticAt ℂ f z) ↔ _
  rw [← hf.meromorphicOrderAt_nonneg_iff_analyticAt, not_le]

/-- Poles have the default complex value zero in Mathlib's normal form. -/
theorem value_zero_at_pole {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicNFAt f z) (hz : z ∈ poleFiber f) : f z = 0 := by
  rcases meromorphicNFAt_iff_analyticAt_or.mp hf with ha | ⟨_, _, hz0⟩
  · exact False.elim (hz ha)
  · exact hz0

/-- A finite value fibre and the pole fibre are disjoint. -/
theorem finiteValueFiber_disjoint_poleFiber (f : ℂ → ℂ) (a : ℂ) :
    Disjoint (finiteValueFiber f a) (poleFiber f) := by
  rw [Set.disjoint_left]
  intro z hfinite hpole
  exact hpole hfinite.1

/-- Nonempty fibres over distinct finite values force a nonconstant function. -/
theorem exists_distinct_values_of_two_fibres {f : ℂ → ℂ} {a b : ℂ}
    (hab : a ≠ b) (ha : (finiteValueFiber f a).Nonempty)
    (hb : (finiteValueFiber f b).Nonempty) : ∃ z w, f z ≠ f w := by
  obtain ⟨z, hz⟩ := ha
  obtain ⟨w, hw⟩ := hb
  exact ⟨z, w, by simpa only [hz.2, hw.2] using hab⟩

end ThreeOmittedValues
