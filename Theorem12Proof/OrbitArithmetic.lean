module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Arithmetic of the selected orbit points

The results below concern the finite index sets and Möbius transformations
used in section 5 of arXiv:2608.26062v2. The completed main theorem is
proved in `Theorem12Research`.
-/

@[expose] public section

namespace ThreeOmittedValues

open Finset

/-- The set `D_m` used to index the orbit points in section 5. -/
def orbitIndices (m : ℕ) : Finset ℕ :=
  (Icc 1 (2 * m)).filter fun d => d.Coprime (2 * m)

/-- Each level has exactly `φ(2m)` indices. -/
theorem card_orbitIndices (m : ℕ) : (orbitIndices m).card = (2 * m).totient := by
  have heq : orbitIndices m =
      (Ico 1 (1 + 2 * m)).filter (fun d => (2 * m).Coprime d) := by
    ext d
    simp only [orbitIndices, mem_filter, mem_Icc, mem_Ico, Nat.coprime_comm]
    omega
  rw [heq]
  exact Nat.filter_coprime_Ico_eq_totient (2 * m) 1

/-- Doubling an integer does not decrease its Euler totient. -/
theorem totient_le_totient_two_mul (m : ℕ) : m.totient ≤ (2 * m).totient := by
  have h := Nat.totient_super_multiplicative 2 m
  simpa only [Nat.totient_two, one_mul] using h

/-- The congruence construction of the matrices in section 5: an admissible
`d` admits an odd inverse `a` modulo `4m`, and the corresponding upper-right
entry `b` is even. -/
theorem exists_orbit_matrix_entries {m d : ℕ} (hm : 2 ≤ m)
    (hd : d ∈ orbitIndices m) :
    ∃ a b : ℕ, 1 ≤ a ∧ a < 4 * m ∧ a * d = 2 * m * b + 1 ∧
      Odd a ∧ Odd d ∧ Even b := by
  have hcop : d.Coprime (2 * m) := (mem_filter.mp hd).2
  have hcop2 : d.Coprime 2 := (Nat.coprime_mul_iff_right.mp hcop).1
  have hcopm : d.Coprime m := (Nat.coprime_mul_iff_right.mp hcop).2
  have hcop4 : d.Coprime (4 * m) := by
    have h := (hcop2.mul_right hcop2).mul_right hcopm
    simpa only [show 2 * 2 = 4 by decide] using h
  have hmodpos : 1 < 4 * m := by omega
  have : NeZero (4 * m) := ⟨by omega⟩
  let a : ℕ := ((d : ZMod (4 * m))⁻¹).val
  have halt : a < 4 * m := ZMod.val_lt _
  have hmod : a * d ≡ 1 [MOD 4 * m] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_mul, Nat.cast_one] using (ZMod.val_inv_mul hcop4)
  have hrem : (a * d) % (4 * m) = 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hmodpos] using hmod
  have hprod : 1 ≤ a * d := by
    have h := Nat.mod_le (a * d) (4 * m)
    omega
  have hapos : 1 ≤ a := by
    by_contra h
    have ha : a = 0 := by omega
    simp [ha] at hprod
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hprod).mp hmod.symm
  have hmod2 : a * d ≡ 1 [MOD 2] :=
    hmod.of_dvd ⟨2 * m, by ring⟩
  have hprododd : (a * d) % 2 = 1 := by
    simpa only [Nat.ModEq, Nat.reduceMod] using hmod2
  have haodd : Odd a := by
    apply Nat.odd_iff.mpr
    have hlt := Nat.mod_lt a (by decide : 0 < 2)
    by_contra h
    have hz : a % 2 = 0 := by omega
    have : (a * d) % 2 = 0 := by simp [Nat.mul_mod, hz]
    omega
  have hdodd : Odd d := by
    apply Nat.odd_iff.mpr
    have hlt := Nat.mod_lt d (by decide : 0 < 2)
    by_contra h
    have hz : d % 2 = 0 := by omega
    have : (a * d) % 2 = 0 := by simp [Nat.mul_mod, hz]
    omega
  refine ⟨a, 2 * k, hapos, halt, ?_, haodd, hdodd, ⟨k, by omega⟩⟩
  calc
    a * d = 1 + 4 * m * k := hk
    _ = 2 * m * (2 * k) + 1 := by ring

/-- Algebraic identity used to locate each selected Möbius orbit point. -/
theorem mobius_orbit_identity {a b c d z : ℂ}
    (hc : c ≠ 0) (hden : c * z + d ≠ 0) (hdet : a * d - c * b = 1) :
    (a * z + b) / (c * z + d) = a / c - 1 / (c * (c * z + d)) := by
  have hden' : z * c + d ≠ 0 := by simpa only [mul_comm] using hden
  field_simp [hc, hden, hden']
  linear_combination -hdet

/-- The imaginary part of a real determinant-one Möbius transformation.
This is the height formula used for the selected orbit points. -/
theorem mobius_imaginary_part {a b c d : ℝ} {z : ℂ}
    (hdet : a * d - c * b = 1) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im =
      z.im / ((c * z.re + d) ^ 2 + (c * z.im) ^ 2) := by
  have hnum : (a * z.im) * (c * z.re + d) - (a * z.re + b) * (c * z.im) = z.im := by
    linear_combination z.im * hdet
  simp only [Complex.div_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply,
    zero_mul, add_zero, sub_zero, ← sub_div, ← pow_two, hnum]

end ThreeOmittedValues
