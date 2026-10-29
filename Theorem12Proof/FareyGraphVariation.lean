module

public import Theorem12Proof.FareyFiniteVariation
public import Theorem12Proof.PastedFareyGraph
public import Theorem12Proof.GraphTopology
import Mathlib.Tactic

/-!
# Uniform local length bounds for the Farey graph

The graph over every integer interval has variation at most two. Global
rectifiability after compactifying infinity requires a separate summation.
-/

@[expose] public section

open Complex Set
open scoped ENNReal

namespace ThreeOmittedValues

theorem eVariationOn_add_complex_le (f g : ℝ → ℂ) (s : Set ℝ) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        (∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)

theorem eVariationOn_ofReal (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => (f x : ℂ)) s = eVariationOn f s := by
  simp only [eVariationOn, Complex.isometry_ofReal.edist_eq]

theorem edist_ofReal_mul_I (x y : ℝ) :
    edist ((x : ℂ) * Complex.I) ((y : ℂ) * Complex.I) = edist x y := by
  have hd : dist ((x : ℂ) * Complex.I) ((y : ℂ) * Complex.I) = dist x y := by
    rw [dist_eq_norm, ← sub_mul, norm_mul, Complex.norm_I, mul_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.dist_eq]
    exact Real.norm_eq_abs _
  simpa only [edist_dist] using congrArg ENNReal.ofReal hd

theorem eVariationOn_ofReal_mul_I (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => (f x : ℂ) * Complex.I) s = eVariationOn f s := by
  simp only [eVariationOn, edist_ofReal_mul_I]

theorem graphMap_variation_le (h : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (graphMap h) s ≤ eVariationOn id s + eVariationOn h s := by
  have hadd := eVariationOn_add_complex_le (fun x => (x : ℂ))
    (fun x => (h x : ℂ) * Complex.I) s
  have hcast : eVariationOn (fun x : ℝ => (x : ℂ)) s = eVariationOn id s :=
    eVariationOn_ofReal id s
  rw [hcast, eVariationOn_ofReal_mul_I] at hadd
  simpa only [graphMap] using! hadd

theorem pastedFareyHeight_variation_unit (levels : ℤ → ℕ) (n : ℤ) :
    eVariationOn (pastedFareyHeight levels) (Icc (n : ℝ) ((n : ℝ) + 1)) ≤ 1 := by
  let interval : Set ℝ := Icc (n : ℝ) ((n : ℝ) + 1)
  have heq : EqOn (pastedFareyHeight levels)
      (chainHeight (sternBrocotEdges (levels n)) ∘ fun x : ℝ => x - n) interval := by
    intro x hx
    exact pastedFareyHeight_eq_on_unit levels n hx
  rw [eVariationOn.congr heq]
  have hmono : MonotoneOn (fun x : ℝ => x - n) interval := by
    intro x hx y hy hxy
    linarith
  have hmap : MapsTo (fun x : ℝ => x - n) interval (Icc 0 1) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  exact (eVariationOn.comp_le_of_monotoneOn _ _ hmono hmap).trans
    (sternBrocot_chainHeight_variation_le_one (levels n))

/-- Uniform length bound on every unit interval, including across the
integer endpoints where the adjacent chains meet. -/
theorem pastedFareyGraph_variation_unit (levels : ℤ → ℕ) (n : ℤ) :
    eVariationOn (graphMap (pastedFareyHeight levels))
      (Icc (n : ℝ) ((n : ℝ) + 1)) ≤ 2 := by
  have h := graphMap_variation_le (pastedFareyHeight levels)
    (Icc (n : ℝ) ((n : ℝ) + 1))
  have hid : eVariationOn id (Icc (n : ℝ) ((n : ℝ) + 1)) = 1 := by
    rw [eVariationOn_id_Icc]
    simp
  rw [hid] at h
  calc
    _ ≤ 1 + eVariationOn (pastedFareyHeight levels) (Icc (n : ℝ) ((n : ℝ) + 1)) := h
    _ ≤ 1 + 1 := add_le_add (le_refl 1) (pastedFareyHeight_variation_unit levels n)
    _ = 2 := by norm_num

end ThreeOmittedValues
