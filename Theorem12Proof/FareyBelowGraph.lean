module

public import Theorem12Proof.PastedFareyGraph
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# A Farey-edge graph below a positive continuous function

This constructs the graph-height part of the paper's Farey boundary from
finite Stern–Brocot chains. Identification of every global edge and cusp,
and the conformal boundary extension, are separate obligations.
-/

@[expose] public section

open Set

namespace ThreeOmittedValues

/-- Every positive continuous comparison graph has an independently chosen
finite refinement over each integer interval, lying strictly below it. -/
theorem exists_farey_height_below_positive (β : ℝ → ℝ)
    (hβcont : Continuous β) (hβpos : ∀ x, 0 < β x) :
    ∃ levels : ℤ → ℕ,
      (∀ n, 1 ≤ levels n) ∧ Continuous (pastedFareyHeight levels) ∧
      ∀ x, 0 ≤ pastedFareyHeight levels x ∧ pastedFareyHeight levels x < β x := by
  have hex (n : ℤ) : ∃ k : ℕ, 1 ≤ k ∧
      ∀ x ∈ Icc (n : ℝ) ((n : ℝ) + 1),
        1 / (2 * ((k + 1 : ℕ) : ℝ)) < β x := by
    have hne : (Icc (n : ℝ) ((n : ℝ) + 1)).Nonempty := ⟨n, by constructor <;> linarith⟩
    obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hβcont.continuousOn
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (hβpos x₀)
    refine ⟨k + 1, by omega, ?_⟩
    intro x hx
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hden : (k : ℝ) + 1 ≤ 2 * (((k + 1 + 1 : ℕ) : ℝ)) := by
      push_cast
      linarith
    have hcmp : 1 / (2 * (((k + 1 + 1 : ℕ) : ℝ))) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le hkpos hden
    exact (hcmp.trans_lt hk).trans_le (hmin hx)
  choose levels hlevels hbelow using hex
  refine ⟨levels, hlevels, pastedFareyHeight_continuous levels, ?_⟩
  intro x
  let n : ℤ := ⌊x⌋
  have hx : x ∈ Icc (n : ℝ) ((n : ℝ) + 1) :=
    ⟨Int.floor_le x, (Int.lt_floor_add_one x).le⟩
  exact ⟨pastedFareyHeight_nonneg levels x,
    (pastedFareyHeight_bound_on_unit levels n hx).trans_lt (hbelow n x hx)⟩

end ThreeOmittedValues
