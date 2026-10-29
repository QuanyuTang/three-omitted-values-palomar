module

public import Theorem12Proof.FareyEdgeMobius
public import Theorem12Proof.FareyGraphIdentification
public import Theorem12Proof.FareyTranslated
import Mathlib.Tactic

/-!
# Real boundary values on the actual Farey graph

Every non-real point of the pasted graph lies on a determinant-one
semicircle, so the modular lambda function takes a real value there.
-/

@[expose] public section

open Complex UpperHalfPlane NoWanderingDomains Set
open scoped MatrixGroups ModularForm Manifold

namespace ThreeOmittedValues

theorem modularLambdaH_real_on_globalFareyArcs (levels : ℤ → ℕ) {z : ℂ}
    (hz : z ∈ globalFareyArcs levels) (hzim : 0 < z.im) :
    (modularLambdaH z).im = 0 := by
  obtain ⟨n, hn⟩ := hz
  obtain ⟨e, he, hleft, hright, hheight⟩ := hn
  obtain ⟨hb, hd, _hdet, _hsum⟩ := sternBrocotEdges_good (levels n) he
  have hbpos : (0 : ℝ) < e.left.denominator := by exact_mod_cast (show 0 < e.left.denominator by omega)
  have hdpos : (0 : ℝ) < e.right.denominator := by exact_mod_cast (show 0 < e.right.denominator by omega)
  let a : ℤ := translatedNumerator n e.left
  let b : ℤ := e.left.denominator
  let c : ℤ := translatedNumerator n e.right
  let d : ℤ := e.right.denominator
  have hdet : c * b - a * d = 1 := by
    have h := sternBrocotEdges_translated_determinant (levels n) he n
    dsimp [a, b, c, d]
    nlinarith [h]
  have hsquare := edgeHeight_sq_of_inside e hleft hright
  rw [← hheight] at hsquare
  simp only [Complex.sub_re, Complex.sub_im, Complex.intCast_re, Complex.intCast_im,
    sub_zero] at hsquare
  have hleftid : (b : ℝ) * z.re - a =
      (e.left.denominator : ℝ) * ((z.re - n) - endpointCoordinate e.left) := by
    dsimp [a, b, translatedNumerator, endpointCoordinate]
    push_cast
    field_simp
    ring
  have hrightid : (c : ℝ) - (d : ℝ) * z.re =
      (e.right.denominator : ℝ) * (endpointCoordinate e.right - (z.re - n)) := by
    dsimp [c, d, translatedNumerator, endpointCoordinate]
    push_cast
    field_simp
    ring
  have hcircle : ((b : ℝ) * z.re - a) * ((c : ℝ) - (d : ℝ) * z.re) =
      ((b : ℝ) * (d : ℝ)) * z.im ^ 2 := by
    rw [hleftid, hrightid]
    calc
      _ = ((e.left.denominator : ℝ) * e.right.denominator) *
          (((z.re - n) - endpointCoordinate e.left) *
            (endpointCoordinate e.right - (z.re - n))) := by ring
      _ = _ := by rw [← hsquare]; rfl
  let τ : UpperHalfPlane := ⟨z, hzim⟩
  exact modularLambdaH_real_on_farey_semicircle a b c d hdet τ hcircle

end ThreeOmittedValues
