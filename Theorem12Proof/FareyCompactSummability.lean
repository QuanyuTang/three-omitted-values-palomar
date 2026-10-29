module

public import Theorem12Proof.FareyCompactLocal
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# Summability of the compactification's tail bounds

The constants controlling the compactified Farey graph form a summable
family over all integer intervals.
-/

@[expose] public section

open Set
open scoped ENNReal NNReal

namespace ThreeOmittedValues

theorem summable_compactUnitLipschitz : Summable compactUnitLipschitz := by
  have hbase : Summable (fun n : ℤ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hsingle : Summable (fun n : ℤ => if n = 0 then (6 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (0 : ℤ)).subset
    intro n hn
    by_contra hn0
    have hn0' : n ≠ 0 := by simpa using hn0
    simp [Function.mem_support, hn0'] at hn
  have hmajor : Summable (fun n : ℤ => (if n = 0 then (6 : ℝ) else 0) +
      6 * (1 / (n : ℝ) ^ (2 : ℕ))) := hsingle.add (hbase.mul_left 6)
  have hreal : Summable (fun n : ℤ => 6 / (1 + (n : ℝ) ^ 2)) := by
    apply hmajor.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      by_cases hn : n = 0
      · simp [hn]
      · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        have hpos : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hn0
        simp only [hn, ite_false, zero_add]
        calc
          6 / (1 + (n : ℝ) ^ 2) ≤ 6 / (n : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left (by norm_num) hpos (by linarith)
          _ = 6 * (1 / (n : ℝ) ^ (2 : ℕ)) := by ring
  apply NNReal.summable_coe.1
  simpa only [compactUnitLipschitz] using! hreal

theorem compactUnitLipschitz_tsum_ne_top :
    (∑' n : ℤ, (compactUnitLipschitz n : ℝ≥0∞)) ≠ ⊤ :=
  ENNReal.tsum_coe_ne_top_iff_summable.mpr summable_compactUnitLipschitz

end ThreeOmittedValues
