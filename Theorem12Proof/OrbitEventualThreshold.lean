module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# A quantitative tail threshold

Choose one natural-number threshold large enough for the logarithm and the
two elementary quadratic inequalities used in the orbit construction.
-/

@[expose] public section

namespace ThreeOmittedValues

theorem exists_orbit_threshold {A U C : ℝ} (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ m : ℕ, N ≤ m →
      1 ≤ Real.log (m : ℝ) ∧ U ≤ (m : ℝ) ^ 2 ∧ 2 * C ≤ A * (m : ℝ) ^ 2 := by
  let R : ℝ := Real.exp 1 + U + (2 * C / A) + 2
  obtain ⟨n, hn⟩ := exists_nat_gt R
  let N := max 2 n
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro m hm
  have hmn : (n : ℝ) ≤ m := by
    have : n ≤ m := by dsimp [N] at hm; omega
    exact_mod_cast this
  have hmR : R < (m : ℝ) := hn.trans_le hmn
  have hm1 : (1 : ℝ) ≤ m := by
    have : 2 ≤ m := by dsimp [N] at hm; omega
    exact_mod_cast (show 1 ≤ m by omega)
  have hquot : 0 < 2 * C / A := by positivity
  have hexp : 0 < Real.exp 1 := Real.exp_pos _
  have hUbound : U ≤ (m : ℝ) := by dsimp [R] at hmR; linarith
  have hCbound : 2 * C / A ≤ (m : ℝ) := by dsimp [R] at hmR; linarith
  have hexpbound : Real.exp 1 ≤ (m : ℝ) := by dsimp [R] at hmR; linarith
  have hmsq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    have h := mul_nonneg (show 0 ≤ (m : ℝ) by positivity) (show 0 ≤ (m : ℝ) - 1 by linarith)
    nlinarith
  refine ⟨?_, hUbound.trans hmsq, ?_⟩
  · have h := Real.log_le_log hexp hexpbound
    simpa using h
  · simpa only [mul_comm] using (div_le_iff₀ hA).mp (hCbound.trans hmsq)

end ThreeOmittedValues
