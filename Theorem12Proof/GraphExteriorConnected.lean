module

public import Theorem12Proof.GraphTopology
import Mathlib.Tactic

/-!
# Connectedness near infinity above a graph

Intersecting a nonnegative graph domain with the exterior of a disk
centered at `-i` gives another domain above a continuous graph.
-/

@[expose] public section

open Complex Metric Set

namespace ThreeOmittedValues

noncomputable def exteriorBump (R x : ℝ) : ℝ :=
  Real.sqrt (max 0 (R ^ 2 - x ^ 2)) - 1

theorem continuous_exteriorBump (R : ℝ) : Continuous (exteriorBump R) := by
  unfold exteriorBump
  fun_prop

theorem upperGraphDomain_inter_exterior_eq {h : ℝ → ℝ} (h0 : ∀ x, 0 ≤ h x)
    {R : ℝ} (hR : 0 ≤ R) :
    upperGraphDomain h ∩ {z : ℂ | R < ‖z + Complex.I‖} =
      upperGraphDomain (fun x => max (h x) (exteriorBump R x)) := by
  ext z
  have hnorm : ‖z + Complex.I‖ ^ 2 = z.re ^ 2 + (z.im + 1) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, add_zero]
    ring
  let s := Real.sqrt (max 0 (R ^ 2 - z.re ^ 2))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = max 0 (R ^ 2 - z.re ^ 2) := Real.sq_sqrt (le_max_left _ _)
  constructor
  · rintro ⟨hzΩ, hzout⟩
    change R < ‖z + Complex.I‖ at hzout
    have hy : 0 < z.im := (h0 z.re).trans_lt hzΩ
    have hnormgt : R ^ 2 < ‖z + Complex.I‖ ^ 2 := by
      nlinarith [norm_nonneg (z + Complex.I)]
    have hslt : s < z.im + 1 := by
      by_cases hd : 0 ≤ R ^ 2 - z.re ^ 2
      · rw [max_eq_right hd] at hs2
        nlinarith
      · have hm : max 0 (R ^ 2 - z.re ^ 2) = 0 := max_eq_left (le_of_not_ge hd)
        have hs : s = 0 := by simp [s, hm]
        linarith
    change max (h z.re) (exteriorBump R z.re) < z.im
    apply max_lt_iff.mpr
    refine ⟨hzΩ, ?_⟩
    change s - 1 < z.im
    linarith
  · intro hz
    change max (h z.re) (exteriorBump R z.re) < z.im at hz
    obtain ⟨hzΩ, hzB⟩ := max_lt_iff.mp hz
    have hy : 0 < z.im := (h0 z.re).trans_lt hzΩ
    have hslt : s < z.im + 1 := by
      change s - 1 < z.im at hzB
      linarith
    have hmax : R ^ 2 - z.re ^ 2 ≤ max 0 (R ^ 2 - z.re ^ 2) := le_max_right _ _
    have hnormgt : R ^ 2 < ‖z + Complex.I‖ ^ 2 := by nlinarith
    refine ⟨hzΩ, ?_⟩
    change R < ‖z + Complex.I‖
    nlinarith [norm_nonneg (z + Complex.I)]

theorem upperGraphDomain_inter_exterior_preconnected {h : ℝ → ℝ}
    (hh : Continuous h) (h0 : ∀ x, 0 ≤ h x) {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected (upperGraphDomain h ∩ {z : ℂ | R < ‖z + Complex.I‖}) := by
  rw [upperGraphDomain_inter_exterior_eq h0 hR]
  have hk : Continuous (fun x => max (h x) (exteriorBump R x)) :=
    hh.max (continuous_exteriorBump R)
  haveI : SimplyConnectedSpace (upperGraphDomain (fun x => max (h x) (exteriorBump R x))) :=
    upperGraphDomain_simplyConnected hk
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

end ThreeOmittedValues
