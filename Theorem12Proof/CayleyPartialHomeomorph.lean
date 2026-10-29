module

public import Theorem12Proof.FareyCompactEmbedding
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Tactic

/-!
# The Cayley map as a partial homeomorphism

The transform is a homeomorphism from the plane without `-i` onto the
plane without `1`. This formulation allows frontier calculations to use
Mathlib's theorem for open partial homeomorphisms.
-/

@[expose] public section

open Complex Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem cayleyToHalfPlane_add_I_ne_zero {w : ℂ} (hw : w ≠ 1) :
    cayleyToHalfPlane w + Complex.I ≠ 0 := by
  have hden : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have heq : cayleyToHalfPlane w + Complex.I = (2 * Complex.I) / (1 - w) := by
    unfold cayleyToHalfPlane
    field_simp
    ring
  rw [heq]
  exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hden

theorem cayleyToHalfPlane_halfPlaneToCayley_of_denominator {z : ℂ}
    (hz : z + Complex.I ≠ 0) : cayleyToHalfPlane (halfPlaneToCayley z) = z := by
  have hne : 1 - halfPlaneToCayley z ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (halfPlaneToCayley_ne_one_of_denominator hz))
  unfold cayleyToHalfPlane halfPlaneToCayley
  field_simp
  ring

theorem halfPlaneToCayley_cayleyToHalfPlane_of_ne_one {w : ℂ}
    (hw : w ≠ 1) : halfPlaneToCayley (cayleyToHalfPlane w) = w := by
  have hden : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hne : cayleyToHalfPlane w + Complex.I ≠ 0 := cayleyToHalfPlane_add_I_ne_zero hw
  unfold cayleyToHalfPlane halfPlaneToCayley
  field_simp
  ring

noncomputable def cayleyPartialHomeomorph : OpenPartialHomeomorph ℂ ℂ where
  toFun := halfPlaneToCayley
  invFun := cayleyToHalfPlane
  source := {z | z + Complex.I ≠ 0}
  target := {w | w ≠ 1}
  map_source' := fun _ hz => halfPlaneToCayley_ne_one_of_denominator hz
  map_target' := fun _ hw => cayleyToHalfPlane_add_I_ne_zero hw
  left_inv' := fun _ hz => cayleyToHalfPlane_halfPlaneToCayley_of_denominator hz
  right_inv' := fun _ hw => halfPlaneToCayley_cayleyToHalfPlane_of_ne_one hw
  open_source := by
    exact (isOpen_ne : IsOpen {z : ℂ | z ≠ 0}).preimage (continuous_id.add continuous_const)
  open_target := isOpen_ne
  continuousOn_toFun := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    unfold halfPlaneToCayley
    exact (continuousAt_id.sub continuousAt_const).div (continuousAt_id.add continuousAt_const) hz
  continuousOn_invFun := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    unfold cayleyToHalfPlane
    have hne : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
    exact (continuousAt_const.mul (continuousAt_const.add continuousAt_id)).div
      (continuousAt_const.sub continuousAt_id) hne

end ThreeOmittedValues
