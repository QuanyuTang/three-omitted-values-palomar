module

public import Theorem12Proof.FareyCurves
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic

/-!
# Variation of the height of a semicircle

On a semicircle the height rises to half its width and falls by the same
amount. This is an ingredient for proving that the Farey boundary is
rectifiable; it does not yet prove rectifiability of the infinite graph.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ThreeOmittedValues

noncomputable def semicircleHeight (a b x : ℝ) : ℝ := Real.sqrt ((x - a) * (b - x))

theorem semicircleHeight_monotone_left {a b : ℝ} (hab : a ≤ b) :
    MonotoneOn (semicircleHeight a b) (Icc a ((a + b) / 2)) := by
  intro x hx y hy hxy
  unfold semicircleHeight
  apply Real.sqrt_le_sqrt
  have hfactor : 0 ≤ (y - x) * (a + b - x - y) := by
    apply mul_nonneg (sub_nonneg.mpr hxy)
    linarith [hx.2, hy.2]
  nlinarith

theorem semicircleHeight_antitone_right {a b : ℝ} (hab : a ≤ b) :
    AntitoneOn (semicircleHeight a b) (Icc ((a + b) / 2) b) := by
  intro x hx y hy hxy
  unfold semicircleHeight
  apply Real.sqrt_le_sqrt
  have hfactor : 0 ≤ (y - x) * (x + y - a - b) := by
    apply mul_nonneg (sub_nonneg.mpr hxy)
    linarith [hx.1, hy.1]
  nlinarith

theorem eVariationOn_neg_real (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => -f x) s = eVariationOn f s := by
  simp only [eVariationOn, edist_neg_neg]

/-- The total vertical variation over the entire semicircle is its width. -/
theorem semicircleHeight_variation {a b : ℝ} (hab : a ≤ b) :
    eVariationOn (semicircleHeight a b) (Icc a b) = ENNReal.ofReal (b - a) := by
  let m := (a + b) / 2
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hleft : semicircleHeight a b a = 0 := by simp [semicircleHeight]
  have hright : semicircleHeight a b b = 0 := by simp [semicircleHeight]
  have hmid : semicircleHeight a b m = (b - a) / 2 := by
    unfold semicircleHeight
    have heq : (m - a) * (b - m) = ((b - a) / 2) ^ 2 := by dsimp [m]; ring
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
  have hlmono : MonotoneOn (semicircleHeight a b) (Icc a m) :=
    semicircleHeight_monotone_left hab
  have hl := hlmono.eVariationOn_eq (show a ∈ Icc a m from ⟨le_rfl, ham⟩)
    (show m ∈ Icc a m from ⟨ham, le_rfl⟩)
  simp only [inter_self, hleft, hmid, sub_zero] at hl
  have hranti : AntitoneOn (semicircleHeight a b) (Icc m b) :=
    semicircleHeight_antitone_right hab
  have hrmono : MonotoneOn (fun x => -semicircleHeight a b x) (Icc m b) := by
    intro x hx y hy hxy
    exact neg_le_neg (hranti hx hy hxy)
  have hr := hrmono.eVariationOn_eq (show m ∈ Icc m b from ⟨le_rfl, hmb⟩)
    (show b ∈ Icc m b from ⟨hmb, le_rfl⟩)
  simp only [inter_self, eVariationOn_neg_real, hright, hmid, neg_zero, sub_neg_eq_add,
    zero_add] at hr
  have hsplit := eVariationOn.Icc_add_Icc (semicircleHeight a b) (s := univ)
    ham hmb (by simp : m ∈ (univ : Set ℝ))
  simp only [univ_inter] at hsplit
  rw [← hsplit, hl, hr, ← ENNReal.ofReal_add (by linarith : 0 ≤ (b - a) / 2)]
  · congr 1
    ring
  · linarith

theorem edgeHeight_variation {e : RationalEdge}
    (he : endpointCoordinate e.left ≤ endpointCoordinate e.right) :
    eVariationOn (edgeHeight e)
      (Icc (endpointCoordinate e.left) (endpointCoordinate e.right)) =
      ENNReal.ofReal (edgeWidth e) := by
  have hid : edgeHeight e = semicircleHeight (endpointCoordinate e.left)
      (endpointCoordinate e.right) := by
    funext x
    rfl
  rw [hid]
  simpa only [edgeWidth] using semicircleHeight_variation he

end ThreeOmittedValues
