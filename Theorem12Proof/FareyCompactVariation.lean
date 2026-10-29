module

public import Theorem12Proof.FareyCompactSummability
import Mathlib.Tactic

/-!
# Finite variation of the compactified Farey graph

Summing the local Cayley contraction bounds over integer intervals gives
finite variation on the whole real parameter line. The extension through
infinity to a closed Jordan parametrization is a subsequent step.
-/

@[expose] public section

open Set NoWanderingDomains
open scoped ENNReal NNReal

namespace ThreeOmittedValues

theorem compactFareyGraph_variation_interval_le (levels : ℤ → ℕ)
    {a b : ℝ} (hab : a ≤ b) :
    eVariationOn (halfPlaneToCayley ∘ graphMap (pastedFareyHeight levels)) (Icc a b) ≤
      (∑' n : ℤ, (compactUnitLipschitz n : ℝ≥0∞)) * 2 := by
  classical
  let A : ℤ := ⌊a⌋
  let B : ℤ := ⌊b⌋ + 1
  have hA : (A : ℝ) ≤ a := Int.floor_le a
  have hB : b ≤ (B : ℝ) := by
    have h := Int.lt_floor_add_one b
    simpa only [B, Int.cast_add, Int.cast_one] using h.le
  have hAB : A ≤ B := by
    have h : (A : ℝ) ≤ (B : ℝ) := hA.trans (hab.trans hB)
    exact_mod_cast h
  let k : ℕ := (B - A).toNat
  have hk : (k : ℤ) = B - A := Int.toNat_of_nonneg (sub_nonneg.mpr hAB)
  have hkR : (k : ℝ) = (B : ℝ) - (A : ℝ) := by exact_mod_cast hk
  let X : ℕ → ℝ := fun i => (A : ℝ) + (i : ℝ)
  have hX : Monotone X := by
    intro i j hij
    dsimp [X]
    have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  have hX0 : X 0 = (A : ℝ) := by simp [X]
  have hXk : X k = (B : ℝ) := by dsimp [X]; linarith
  have hcover : Icc a b ⊆ Icc (X 0) (X k) := by
    rw [hX0, hXk]
    exact Icc_subset_Icc hA hB
  let Q : ℤ → ℝ≥0∞ := fun n => (compactUnitLipschitz n : ℝ≥0∞)
  let j : ℕ → ℤ := fun i => A + (i : ℤ)
  have hj : Function.Injective j := by
    intro i l hil
    have h : (i : ℤ) = (l : ℤ) := add_left_cancel hil
    exact_mod_cast h
  have hsum : (∑ i ∈ Finset.range k, Q (j i)) ≤ ∑' n : ℤ, Q n := by
    have h := (ENNReal.summable : Summable Q).sum_le_tsum
      ((Finset.range k).image j) (fun _ _ => bot_le)
    simpa only [Finset.sum_image hj.injOn] using h
  let G : ℝ → ℂ := halfPlaneToCayley ∘ graphMap (pastedFareyHeight levels)
  have hblocks := eVariationOn.sum' G hX (n := k)
  have hbound (i : ℕ) (hi : i ∈ Finset.range k) :
      eVariationOn G (Icc (X i) (X (i + 1))) ≤ Q (j i) * 2 := by
    have h := compactFareyGraph_variation_unit levels (j i)
    simpa only [G, Q, j, X, Int.cast_add, Int.cast_natCast, Nat.cast_add,
      Nat.cast_one, add_assoc] using h
  calc
    eVariationOn G (Icc a b) ≤ eVariationOn G (Icc (X 0) (X k)) := eVariationOn.mono G hcover
    _ = ∑ i ∈ Finset.range k, eVariationOn G (Icc (X i) (X (i + 1))) := hblocks.symm
    _ ≤ ∑ i ∈ Finset.range k, Q (j i) * 2 := Finset.sum_le_sum hbound
    _ = (∑ i ∈ Finset.range k, Q (j i)) * 2 := by rw [Finset.sum_mul]
    _ ≤ (∑' n : ℤ, Q n) * 2 := by gcongr

theorem compactFareyGraph_variation_all_le (levels : ℤ → ℕ) :
    eVariationOn (halfPlaneToCayley ∘ graphMap (pastedFareyHeight levels)) univ ≤
      (∑' n : ℤ, (compactUnitLipschitz n : ℝ≥0∞)) * 2 := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  refine iSup_le fun ⟨a, b⟩ => iSup_le fun hab => ?_
  simp only [mem_setOf_eq, mem_univ, true_and] at hab
  simpa only [univ_inter] using compactFareyGraph_variation_interval_le levels hab

/-- The compactified graph has finite total variation even though its
parameter runs over the entire real line. -/
theorem compactFareyGraph_boundedVariation (levels : ℤ → ℕ) :
    BoundedVariationOn (halfPlaneToCayley ∘ graphMap (pastedFareyHeight levels)) univ := by
  apply ne_top_of_le_ne_top _ (compactFareyGraph_variation_all_le levels)
  exact ENNReal.mul_ne_top compactUnitLipschitz_tsum_ne_top (by norm_num)

end ThreeOmittedValues
