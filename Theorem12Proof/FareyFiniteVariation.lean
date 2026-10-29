module

public import Theorem12Proof.VariationMax
import Mathlib.Tactic

/-!
# Uniform variation bound for finite Farey chains

The height of a finite chain has variation at most one on the unit
interval, independently of the refinement depth.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ThreeOmittedValues

theorem edgeHeight_variation_unit {e : RationalEdge}
    (hleft : 0 ≤ endpointCoordinate e.left)
    (hinc : endpointCoordinate e.left ≤ endpointCoordinate e.right)
    (hright : endpointCoordinate e.right ≤ 1) :
    eVariationOn (edgeHeight e) (Icc (0 : ℝ) 1) = ENNReal.ofReal (edgeWidth e) := by
  have hleftvar : eVariationOn (edgeHeight e) (Icc 0 (endpointCoordinate e.left)) = 0 := by
    have heq : EqOn (edgeHeight e) (fun _ => 0) (Icc 0 (endpointCoordinate e.left)) := by
      intro x hx
      exact edgeHeight_eq_zero_of_le_left e hinc hx.2
    rw [eVariationOn.congr heq]
    simp [eVariationOn]
  have hrightvar : eVariationOn (edgeHeight e) (Icc (endpointCoordinate e.right) 1) = 0 := by
    have heq : EqOn (edgeHeight e) (fun _ => 0) (Icc (endpointCoordinate e.right) 1) := by
      intro x hx
      exact edgeHeight_eq_zero_of_right_le e hinc hx.1
    rw [eVariationOn.congr heq]
    simp [eVariationOn]
  have hsplit1 := eVariationOn.Icc_add_Icc (edgeHeight e) (s := univ)
    hleft hinc (by simp : endpointCoordinate e.left ∈ (univ : Set ℝ))
  have hsplit2 := eVariationOn.Icc_add_Icc (edgeHeight e) (s := univ)
    (hleft.trans hinc) hright (by simp : endpointCoordinate e.right ∈ (univ : Set ℝ))
  simp only [univ_inter, hleftvar, zero_add] at hsplit1
  simp only [univ_inter, hrightvar, add_zero] at hsplit2
  rw [← hsplit2, ← hsplit1, edgeHeight_variation hinc]

def IsUnitIntervalEdge (e : RationalEdge) : Prop :=
  0 ≤ endpointCoordinate e.left ∧
  endpointCoordinate e.left ≤ endpointCoordinate e.right ∧
  endpointCoordinate e.right ≤ 1

theorem edgeWidths_nonneg (es : List RationalEdge)
    (h : ∀ e ∈ es, IsUnitIntervalEdge e) : 0 ≤ (es.map edgeWidth).sum := by
  induction es with
  | nil => simp
  | cons e es ih =>
      have he : IsUnitIntervalEdge e := h e (by simp)
      have ht : ∀ e ∈ es, IsUnitIntervalEdge e := fun e he => h e (by simp [he])
      have hw : 0 ≤ edgeWidth e := by dsimp [edgeWidth]; linarith [he.2.1]
      simpa only [List.map_cons, List.sum_cons] using add_nonneg hw (ih ht)

theorem chainHeight_variation_le_widths (es : List RationalEdge)
    (h : ∀ e ∈ es, IsUnitIntervalEdge e) :
    eVariationOn (chainHeight es) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (es.map edgeWidth).sum := by
  induction es with
  | nil => simp [chainHeight, eVariationOn]
  | cons e es ih =>
      have he : IsUnitIntervalEdge e := h e (by simp)
      have ht : ∀ e ∈ es, IsUnitIntervalEdge e := fun e he => h e (by simp [he])
      have hw : 0 ≤ edgeWidth e := by dsimp [edgeWidth]; linarith [he.2.1]
      have hsum : 0 ≤ (es.map edgeWidth).sum := edgeWidths_nonneg es ht
      have hevar := edgeHeight_variation_unit he.1 he.2.1 he.2.2
      have htvar := ih ht
      change eVariationOn (fun x => max (edgeHeight e x) (chainHeight es x))
          (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (edgeWidth e + (es.map edgeWidth).sum)
      calc
        _ ≤ eVariationOn (edgeHeight e) (Icc (0 : ℝ) 1) +
            eVariationOn (chainHeight es) (Icc (0 : ℝ) 1) := eVariationOn_max_le _ _ _
        _ ≤ ENNReal.ofReal (edgeWidth e) + ENNReal.ofReal (es.map edgeWidth).sum :=
          add_le_add hevar.le htvar
        _ = ENNReal.ofReal (edgeWidth e + (es.map edgeWidth).sum) :=
          (ENNReal.ofReal_add hw hsum).symm

/-- Uniform in the number of Stern–Brocot refinements. -/
theorem sternBrocot_chainHeight_variation_le_one (n : ℕ) :
    eVariationOn (chainHeight (sternBrocotEdges n)) (Icc (0 : ℝ) 1) ≤ 1 := by
  have hvalid : ∀ e ∈ sternBrocotEdges n, IsUnitIntervalEdge e := by
    intro e he
    have hcoords := sternBrocotEdges_coordinates_in_unit n he
    exact ⟨hcoords.1.1, (sternBrocotEdges_strict n he).le, hcoords.2.2⟩
  have h := chainHeight_variation_le_widths (sternBrocotEdges n) hvalid
  simpa only [sternBrocotEdges_sum_width, ENNReal.ofReal_one] using h

end ThreeOmittedValues
