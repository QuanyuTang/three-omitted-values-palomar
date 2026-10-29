module

public import Theorem12Proof.SemicircleVariation
import Mathlib.Tactic

/-!
# Variation of pointwise maxima

An upper bound for the variation of the maximum of two real functions,
used to handle a finite union of semicircle graphs.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ThreeOmittedValues

theorem eVariationOn_max_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => max (f x) (g x)) s ≤ eVariationOn f s + eVariationOn g s := by
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hreal : |max (f (u (i + 1))) (g (u (i + 1))) - max (f (u i)) (g (u i))| ≤
          |f (u (i + 1)) - f (u i)| + |g (u (i + 1)) - g (u i)| := by
        apply (abs_max_sub_max_le_max _ _ _ _).trans
        apply max_le <;> linarith [abs_nonneg (f (u (i + 1)) - f (u i)),
          abs_nonneg (g (u (i + 1)) - g (u i))]
      calc
        edist (max (f (u (i + 1))) (g (u (i + 1))))
            (max (f (u i)) (g (u i))) =
            ENNReal.ofReal |max (f (u (i + 1))) (g (u (i + 1))) -
              max (f (u i)) (g (u i))| := by rw [edist_dist, Real.dist_eq]
        _ ≤ ENNReal.ofReal (|f (u (i + 1)) - f (u i)| +
            |g (u (i + 1)) - g (u i)|) := ENNReal.ofReal_le_ofReal hreal
        _ = edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i)) := by
          rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), edist_dist, edist_dist,
            Real.dist_eq, Real.dist_eq]
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        (∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)

end ThreeOmittedValues
