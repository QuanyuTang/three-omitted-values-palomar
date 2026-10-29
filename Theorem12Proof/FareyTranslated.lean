module

public import Theorem12Proof.SternBrocot
import Mathlib.Tactic

/-!
# Integer translates of finite Farey chains

The determinant-one property survives every integer translate; integer and
half-integer vertices occupy all three primitive parity classes modulo two.
-/

@[expose] public section

namespace ThreeOmittedValues

def translatedNumerator (n : ℤ) (u : RationalEndpoint) : ℤ :=
  (u.numerator : ℤ) + n * (u.denominator : ℤ)

/-- Translating a determinant-one pair by an integer preserves its
determinant, including for negative translations. -/
theorem sternBrocotEdges_translated_determinant (n : ℕ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges n) (k : ℤ) :
    (e.left.denominator : ℤ) * translatedNumerator k e.right -
      translatedNumerator k e.left * (e.right.denominator : ℤ) = 1 := by
  obtain ⟨_, _, hdet, _⟩ := sternBrocotEdges_good n he
  have h : (e.left.denominator : ℤ) * e.right.numerator =
      (e.left.numerator : ℤ) * e.right.denominator + 1 := by exact_mod_cast hdet
  dsimp [translatedNumerator]
  nlinarith [h]

def parityClass (p q : ℤ) : ℤ × ℤ := (p % 2, q % 2)

/-- The vertices `n`, `n + 1/2`, and `n + 1` represent three different
nonzero parity classes. -/
theorem integer_half_integer_parity_classes (n : ℤ) :
    parityClass n 1 ≠ parityClass (2 * n + 1) 2 ∧
    parityClass n 1 ≠ parityClass (n + 1) 1 ∧
    parityClass (2 * n + 1) 2 ≠ parityClass (n + 1) 1 := by
  constructor
  · intro h
    have hsecond := congrArg Prod.snd h
    norm_num [parityClass] at hsecond
  · constructor
    · intro h
      have hfirst := congrArg Prod.fst h
      dsimp [parityClass] at hfirst
      omega
    · intro h
      have hsecond := congrArg Prod.snd h
      norm_num [parityClass] at hsecond

end ThreeOmittedValues
