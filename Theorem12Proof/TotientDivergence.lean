module

public import Theorem12Proof.LogHarmonic
public import Theorem12Proof.OrbitArithmetic
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Tactic

/-!
# Logarithmically weighted totient divergence

The argument uses the elementary identity `∑_{d | n} φ(d) = n`, rather
than a summatory-totient asymptotic. The complete main theorem still needs
the geometric and complex-analytic parts of the paper.
-/

@[expose] public section

open Set

namespace ThreeOmittedValues

/-- A shifted-log version of the needed totient divergence. -/
theorem not_summable_totient_shifted_log :
    ¬ Summable (fun n : ℕ => (Nat.totient n : ℝ) /
      ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1))) := by
  let A : ℕ → ℝ := fun n => (Nat.totient n : ℝ) /
    ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1))
  let B : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have hA0 (n : ℕ) : 0 ≤ A n := by
    dsimp [A]
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 n))))
  have hB0 (n : ℕ) : 0 ≤ B n := by dsimp [B]; positivity
  intro hA
  have hB : Summable B := by
    dsimp [B]
    exact Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hAn : Summable (fun n => ‖A n‖) := by
    have heq : (fun n => ‖A n‖) = A := by
      funext n
      exact Real.norm_of_nonneg (hA0 n)
    rw [heq]
    exact hA
  have hBn : Summable (fun n => ‖B n‖) := by
    have heq : (fun n => ‖B n‖) = B := by
      funext n
      exact Real.norm_of_nonneg (hB0 n)
    rw [heq]
    exact hB
  have hprod : Summable (fun p : ℕ × ℕ => A p.1 * B p.2) :=
    summable_mul_of_summable_norm hAn hBn
  let multiply : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  let C : ℕ → ℝ := fun n => ∑' p : multiply ⁻¹' {n}, A p.1.1 * B p.1.2
  have hC : Summable C := (hprod.hasSum.tsum_fiberwise multiply).summable
  have hterm (n d : ℕ) (hn : 0 < n) (hd : d ∈ n.divisors) :
      (Nat.totient d : ℝ) / ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) ≤
        A d * B (n / d) := by
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hddvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hdle : d ≤ n := Nat.le_of_dvd hn hddvd
    have hkpos : 0 < n / d := Nat.div_pos hdle hdpos
    have hdpos' : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hkpos' : (0 : ℝ) < (n / d : ℕ) := by exact_mod_cast hkpos
    have hlogpos : 0 < Real.log ((d : ℝ) + 1) := Real.log_pos (by linarith)
    have hlogle : Real.log ((d : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hdle 1)
    have hdk : (d : ℝ) * ((n / d : ℕ) : ℝ) = n := by
      exact_mod_cast Nat.mul_div_cancel' hddvd
    have hdenpos : 0 < ((d : ℝ) ^ 2 * ((n / d : ℕ) : ℝ) ^ 2) *
        Real.log ((d : ℝ) + 1) := by positivity
    have hdenle : ((d : ℝ) ^ 2 * ((n / d : ℕ) : ℝ) ^ 2) *
        Real.log ((d : ℝ) + 1) ≤ (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) := by
      calc
        _ ≤ ((d : ℝ) ^ 2 * ((n / d : ℕ) : ℝ) ^ 2) *
              Real.log ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left hlogle (by positivity)
        _ = _ := by rw [← hdk]; ring
    have hfrac := one_div_le_one_div_of_le hdenpos hdenle
    have hmul := mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg (Nat.totient d))
    convert hmul using 1 <;> (try dsimp [A, B]) <;> ring
  have hbound (n : ℕ) : 1 / ((n : ℝ) * Real.log ((n : ℝ) + 1)) ≤ C n := by
    by_cases hn : n = 0
    · subst n
      have : 0 ≤ C 0 := tsum_nonneg (fun p => mul_nonneg (hA0 _) (hB0 _))
      simpa using this
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hlogpos : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
    have hsum : 1 / ((n : ℝ) * Real.log ((n : ℝ) + 1)) =
        ∑ d ∈ n.divisors, (Nat.totient d : ℝ) /
          ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) := by
      rw [← Finset.sum_div, ← Nat.cast_sum, Nat.sum_totient]
      field_simp
    have hfiber : C n = ∑ p ∈ n.divisorsAntidiagonal, A p.1 * B p.2 := by
      dsimp [C]
      rw [show multiply ⁻¹' {n} = (n.divisorsAntidiagonal : Set (ℕ × ℕ)) by
        ext p
        simp [multiply, Nat.mem_divisorsAntidiagonal, hn]]
      exact Finset.tsum_subtype' n.divisorsAntidiagonal (fun p => A p.1 * B p.2)
    rw [hsum, hfiber, Nat.sum_divisorsAntidiagonal (fun x y => A x * B y)]
    exact Finset.sum_le_sum (fun d hd => hterm n d hnpos hd)
  have hharm : Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log ((n : ℝ) + 1))) :=
    hC.of_nonneg_of_le (fun n => by
      apply one_div_nonneg.mpr
      exact mul_nonneg (Nat.cast_nonneg n)
        (Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 n)))) hbound
  exact not_summable_log_harmonic hharm

/-- The precise logarithmically weighted totient series used in the paper
diverges, without assuming an asymptotic for the summatory totient. -/
theorem not_summable_totient_two_mul_log :
    ¬ Summable (fun m : ℕ => (Nat.totient (2 * m) : ℝ) /
      ((m : ℝ) ^ 2 * Real.log (m : ℝ))) := by
  intro hsum
  have htail : Summable (fun n : ℕ => (Nat.totient (2 * (n + 2)) : ℝ) /
      (((n + 2 : ℕ) : ℝ) ^ 2 * Real.log ((n + 2 : ℕ) : ℝ))) := by
    exact (summable_nat_add_iff 2).2 hsum
  have hsmall : Summable (fun n : ℕ => (Nat.totient (n + 2) : ℝ) /
      (((n + 2 : ℕ) : ℝ) ^ 2 * Real.log (((n + 2 : ℕ) : ℝ) + 1))) := by
    apply htail.of_nonneg_of_le
    · intro n
      apply div_nonneg (Nat.cast_nonneg _)
      apply mul_nonneg (sq_nonneg _)
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 + 1 by omega))
    · intro n
      let m := n + 2
      have hm : (1 : ℝ) < m := by dsimp [m]; exact_mod_cast (show 1 < n + 2 by omega)
      have hmpos : (0 : ℝ) < m := by linarith
      have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos hm
      have hlogle : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) :=
        Real.log_le_log hmpos (by linarith)
      have htot : (Nat.totient m : ℝ) ≤ Nat.totient (2 * m) := by
        exact_mod_cast totient_le_totient_two_mul m
      calc
        (Nat.totient m : ℝ) / ((m : ℝ) ^ 2 * Real.log ((m : ℝ) + 1))
            ≤ (Nat.totient m : ℝ) / ((m : ℝ) ^ 2 * Real.log (m : ℝ)) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
            (mul_le_mul_of_nonneg_left hlogle (sq_nonneg _))
        _ ≤ (Nat.totient (2 * m) : ℝ) / ((m : ℝ) ^ 2 * Real.log (m : ℝ)) :=
          div_le_div_of_nonneg_right htot (by positivity)
  have hshifted : Summable (fun n : ℕ => (Nat.totient n : ℝ) /
      ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1))) := by
    exact (summable_nat_add_iff 2).1 hsmall
  exact not_summable_totient_shifted_log hshifted

/-- Indices for all the finite orbit levels in the paper. -/
abbrev OrbitIndex := (m : ℕ) × {d // d ∈ orbitIndices m}

/-- A nonnegative family with the paper's eventual lower bound at every
orbit index has divergent total mass. This is a purely arithmetic reduction;
it does not assert that the required orbit points have been constructed. -/
theorem not_summable_of_orbit_lower_bound (w : OrbitIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) {c : ℝ} (hc : 0 < c)
    (hbound : ∃ M : ℕ, ∀ m ≥ M, ∀ d : {d // d ∈ orbitIndices m},
      c / ((m : ℝ) ^ 2 * Real.log (m : ℝ)) ≤ w ⟨m, d⟩) :
    ¬ Summable w := by
  classical
  obtain ⟨M, hM⟩ := hbound
  let N := max M 2
  intro hsum
  have hlevels : Summable (fun m : ℕ => ∑' d : {d // d ∈ orbitIndices m}, w ⟨m, d⟩) :=
    (summable_sigma_of_nonneg hw).mp hsum |>.2
  have hlevels_tail : Summable (fun n : ℕ =>
      ∑' d : {d // d ∈ orbitIndices (n + N)}, w ⟨n + N, d⟩) :=
    (summable_nat_add_iff N).2 hlevels
  have hsmall : Summable (fun n : ℕ => c * ((Nat.totient (2 * (n + N)) : ℝ) /
      (((n + N : ℕ) : ℝ) ^ 2 * Real.log ((n + N : ℕ) : ℝ)))) := by
    apply hlevels_tail.of_nonneg_of_le
    · intro n
      apply mul_nonneg hc.le
      apply div_nonneg (Nat.cast_nonneg _)
      apply mul_nonneg (sq_nonneg _)
      exact Real.log_nonneg (by
        have : 1 ≤ n + N := by dsimp [N]; omega
        exact_mod_cast this)
    · intro n
      let m := n + N
      change c * ((Nat.totient (2 * m) : ℝ) /
          ((m : ℝ) ^ 2 * Real.log (m : ℝ))) ≤
        ∑' d : {d // d ∈ orbitIndices m}, w ⟨m, d⟩
      have hm : M ≤ m := by dsimp [m, N]; omega
      have hsum_bound : (∑ _d : {d // d ∈ orbitIndices m},
          c / ((m : ℝ) ^ 2 * Real.log (m : ℝ))) ≤
          ∑ d : {d // d ∈ orbitIndices m}, w ⟨m, d⟩ :=
        Finset.sum_le_sum (fun d _ => hM m hm d)
      have hcard : (Fintype.card {d // d ∈ orbitIndices m} : ℝ) = Nat.totient (2 * m) := by
        rw [Fintype.card_coe, card_orbitIndices]
      calc
        _ = (Nat.totient (2 * m) : ℝ) * (c / ((m : ℝ) ^ 2 * Real.log (m : ℝ))) := by ring
        _ ≤ _ := by
          simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, tsum_fintype]
            using hsum_bound
  have hscaled : Summable (fun m : ℕ => c * ((Nat.totient (2 * m) : ℝ) /
      ((m : ℝ) ^ 2 * Real.log (m : ℝ)))) := (summable_nat_add_iff N).1 hsmall
  have hplain : Summable (fun m : ℕ => (Nat.totient (2 * m) : ℝ) /
      ((m : ℝ) ^ 2 * Real.log (m : ℝ))) := by
    have h := hscaled.mul_left c⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] using h
  exact not_summable_totient_two_mul_log hplain

/-- The actual construction only needs the orbit levels `m ≥ N`; points
at earlier levels need not exist in the comparison domain. -/
abbrev OrbitIndexFrom (N : ℕ) :=
  (m : {m : ℕ // N ≤ m}) × {d // d ∈ orbitIndices m.1}

/-- The levelwise lower-bound argument remains valid on any fixed tail of
the orbit levels. -/
theorem not_summable_of_orbit_tail_lower_bound (N : ℕ) (w : OrbitIndexFrom N → ℝ)
    (hw : ∀ i, 0 ≤ w i) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ m : {m : ℕ // N ≤ m}, ∀ d : {d // d ∈ orbitIndices m.1},
      c / ((m.1 : ℝ) ^ 2 * Real.log (m.1 : ℝ)) ≤ w ⟨m, d⟩) :
    ¬ Summable w := by
  classical
  let K := max N 2
  let idx : ℕ → {m : ℕ // N ≤ m} := fun n => ⟨n + K, by dsimp [K]; omega⟩
  have hidx : Function.Injective idx := by
    intro x y h
    have hval := congrArg Subtype.val h
    dsimp [idx] at hval
    omega
  intro hsum
  have hlevels : Summable (fun m : {m : ℕ // N ≤ m} =>
      ∑' d : {d // d ∈ orbitIndices m.1}, w ⟨m, d⟩) :=
    (summable_sigma_of_nonneg hw).mp hsum |>.2
  have hlevels_tail : Summable (fun n : ℕ =>
      ∑' d : {d // d ∈ orbitIndices (idx n).1}, w ⟨idx n, d⟩) :=
    hlevels.comp_injective hidx
  have hsmall : Summable (fun n : ℕ => c * ((Nat.totient (2 * (n + K)) : ℝ) /
      (((n + K : ℕ) : ℝ) ^ 2 * Real.log ((n + K : ℕ) : ℝ)))) := by
    apply hlevels_tail.of_nonneg_of_le
    · intro n
      apply mul_nonneg hc.le
      apply div_nonneg (Nat.cast_nonneg _)
      apply mul_nonneg (sq_nonneg _)
      exact Real.log_nonneg (by
        have : 1 ≤ n + K := by dsimp [K]; omega
        exact_mod_cast this)
    · intro n
      let m := idx n
      change c * ((Nat.totient (2 * m.1) : ℝ) /
          ((m.1 : ℝ) ^ 2 * Real.log (m.1 : ℝ))) ≤
        ∑' d : {d // d ∈ orbitIndices m.1}, w ⟨m, d⟩
      have hsum_bound : (∑ _d : {d // d ∈ orbitIndices m.1},
          c / ((m.1 : ℝ) ^ 2 * Real.log (m.1 : ℝ))) ≤
          ∑ d : {d // d ∈ orbitIndices m.1}, w ⟨m, d⟩ :=
        Finset.sum_le_sum (fun d _ => hbound m d)
      have hcard : (Fintype.card {d // d ∈ orbitIndices m.1} : ℝ) =
          Nat.totient (2 * m.1) := by rw [Fintype.card_coe, card_orbitIndices]
      calc
        _ = (Nat.totient (2 * m.1) : ℝ) * (c / ((m.1 : ℝ) ^ 2 * Real.log (m.1 : ℝ))) := by ring
        _ ≤ _ := by
          simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, tsum_fintype]
            using hsum_bound
  have hscaled : Summable (fun m : ℕ => c * ((Nat.totient (2 * m) : ℝ) /
      ((m : ℝ) ^ 2 * Real.log (m : ℝ)))) := (summable_nat_add_iff K).1 hsmall
  have hplain : Summable (fun m : ℕ => (Nat.totient (2 * m) : ℝ) /
      ((m : ℝ) ^ 2 * Real.log (m : ℝ))) := by
    have h := hscaled.mul_left c⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] using h
  exact not_summable_totient_two_mul_log hplain

end ThreeOmittedValues
