module

public import Theorem12Proof.FareyVertexEdges
public import Theorem12Proof.FareyEdgeMobius
public import Theorem12Proof.FareyTranslated
import Mathlib.Tactic

/-!
# A modular matrix sending infinity to each Farey vertex

An incident determinant-one edge supplies the second column, so this needs
no separate Bézout or rational-cusp axiom.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold

namespace ThreeOmittedValues

theorem pastedFarey_vertex_has_modular_matrix (levels : ℤ → ℕ) (r : ℝ)
    (hr0 : pastedFareyHeight levels r = 0) :
    ∃ (γ : SL(2, ℤ)) (p q : ℤ), 0 < q ∧
      r = (p : ℝ) / (q : ℝ) ∧ γ.val 0 0 = p ∧ γ.val 1 0 = q := by
  obtain ⟨δ, hδ, hisol⟩ := pastedFarey_vertex_isolated levels r
  obtain ⟨n, e, he, _hl, _hr, hinc, _hsquare⟩ :=
    pastedFarey_edge_near_vertex levels hr0 hδ hisol (x := r) (by simpa using hδ)
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
  have hbpos' : 0 < b := by dsimp [b]; exact_mod_cast (show 0 < e.left.denominator by omega)
  have hdpos' : 0 < d := by dsimp [d]; exact_mod_cast (show 0 < e.right.denominator by omega)
  have hleft : (n : ℝ) + endpointCoordinate e.left = (a : ℝ) / (b : ℝ) := by
    dsimp [a, b, translatedNumerator, endpointCoordinate]
    push_cast
    field_simp
    ring
  have hright : (n : ℝ) + endpointCoordinate e.right = (c : ℝ) / (d : ℝ) := by
    dsimp [c, d, translatedNumerator, endpointCoordinate]
    push_cast
    field_simp
    ring
  rcases hinc with hl | hr
  · let γ : SL(2, ℤ) := ⟨!![a, -c; b, -d], by
      rw [Matrix.det_fin_two_of]
      nlinarith [hdet]⟩
    refine ⟨γ, a, b, hbpos', hl.trans hleft, ?_, ?_⟩ <;> simp [γ]
  · let γ : SL(2, ℤ) := fareyEdgeMatrix a b c d hdet
    refine ⟨γ, c, d, hdpos', hr.trans hright, ?_, ?_⟩ <;> simp [γ, fareyEdgeMatrix]

end ThreeOmittedValues
