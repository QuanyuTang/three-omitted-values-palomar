module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The logarithmic harmonic series

This analytic lemma is intended for an elementary proof of the totient
divergence needed by the paper. It is independent of the main theorem.
-/

@[expose] public section

namespace ThreeOmittedValues

/-- The series `∑ 1/(n log(n+1))` diverges. The value at `n = 0` uses
Lean's totalized division and is zero. -/
theorem not_summable_log_harmonic :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log ((n : ℝ) + 1))) := by
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log ((n : ℝ) + 1))
  have hnonneg : ∀ n, 0 ≤ f n := by
    intro n
    apply one_div_nonneg.mpr
    apply mul_nonneg (Nat.cast_nonneg n)
    exact Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 n))
  have hmono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hlogpos : 0 < Real.log ((m : ℝ) + 1) := Real.log_pos (by linarith)
    have hlogle : Real.log ((m : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have hden : (m : ℝ) * Real.log ((m : ℝ) + 1) ≤
        (n : ℝ) * Real.log ((n : ℝ) + 1) :=
      mul_le_mul hmn' hlogle hlogpos.le (by linarith)
    exact one_div_le_one_div_of_le (mul_pos hmpos hlogpos) hden
  intro hsum
  have hcond : Summable (fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) :=
    (summable_condensed_iff_of_nonneg hnonneg hmono).2 hsum
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound (k : ℕ) :
      1 / (((k : ℝ) + 1) * Real.log 2) ≤ (2 : ℝ) ^ k * f (2 ^ k) := by
    have hp : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) _
    have hpow : (2 : ℝ) ^ k + 1 ≤ (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      have := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)
      linarith
    have hlogle : Real.log ((2 : ℝ) ^ k + 1) ≤ ((k : ℝ) + 1) * Real.log 2 := by
      calc
        Real.log ((2 : ℝ) ^ k + 1) ≤ Real.log ((2 : ℝ) ^ (k + 1)) :=
          Real.log_le_log (by positivity) hpow
        _ = ((k : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    have hlogpos : 0 < Real.log ((2 : ℝ) ^ k + 1) := Real.log_pos (by linarith)
    have hcomp := one_div_le_one_div_of_le hlogpos hlogle
    dsimp [f]
    push_cast
    have heq : (2 : ℝ) ^ k * (1 / ((2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k + 1))) =
        1 / Real.log ((2 : ℝ) ^ k + 1) := by
      field_simp
    rw [heq]
    exact hcomp
  have hsmall : Summable (fun k : ℕ => 1 / (((k : ℝ) + 1) * Real.log 2)) :=
    hcond.of_nonneg_of_le (fun k => by positivity) hbound
  have hshift : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
    have hscaled := hsmall.mul_left (Real.log 2)
    apply hscaled.congr
    intro k
    field_simp
  have hharm : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    apply (summable_nat_add_iff 1).1
    simpa using hshift
  exact Real.not_summable_one_div_natCast hharm

end ThreeOmittedValues
