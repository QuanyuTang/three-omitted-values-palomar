module

public import Theorem12Proof.FareyCurves
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Pasting finite Farey chains along the real line

Each integer interval has an independently chosen finite refinement. The
finite height functions vanish at their endpoints, allowing them to be
pasted into a continuous proper graph. The choice of depths below a given
positive comparison function is a separate step.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace ThreeOmittedValues

noncomputable section

/-- The height obtained by pasting independent finite Farey chains. -/
def pastedFareyHeight (levels : ℤ → ℕ) (x : ℝ) : ℝ :=
  chainHeight (sternBrocotEdges (levels ⌊x⌋)) (x - (⌊x⌋ : ℝ))

/-- The pasted height agrees with the selected finite chain on each closed
unit interval, including the common endpoint with the next interval. -/
theorem pastedFareyHeight_eq_on_unit (levels : ℤ → ℕ) (n : ℤ) {x : ℝ}
    (hx : x ∈ Icc (n : ℝ) ((n : ℝ) + 1)) :
    pastedFareyHeight levels x =
      chainHeight (sternBrocotEdges (levels n)) (x - n) := by
  by_cases hlt : x < (n : ℝ) + 1
  · have hf : ⌊x⌋ = n := Int.floor_eq_iff.mpr ⟨hx.1, hlt⟩
    simp only [pastedFareyHeight, hf]
  · have hend : x = (n : ℝ) + 1 := by linarith [hx.2]
    have hzero (k : ℕ) : chainHeight (sternBrocotEdges k) 0 = 0 :=
      sternBrocot_chainHeight_eq_zero_outside k (Or.inl le_rfl)
    have hone (k : ℕ) : chainHeight (sternBrocotEdges k) 1 = 0 :=
      sternBrocot_chainHeight_eq_zero_outside k (Or.inr le_rfl)
    simp [pastedFareyHeight, hend, hzero, hone]

theorem pastedFareyHeight_continuousOn_unit (levels : ℤ → ℕ) (n : ℤ) :
    ContinuousOn (pastedFareyHeight levels) (Icc (n : ℝ) ((n : ℝ) + 1)) := by
  have hg : Continuous (fun x : ℝ =>
      chainHeight (sternBrocotEdges (levels n)) (x - n)) :=
    (continuous_chainHeight _).comp (continuous_id.sub continuous_const)
  apply hg.continuousOn.congr
  intro x hx
  exact pastedFareyHeight_eq_on_unit levels n hx

/-- The locally finite chain of finite graphs is continuous across every
integer boundary. -/
theorem pastedFareyHeight_continuous (levels : ℤ → ℕ) : Continuous (pastedFareyHeight levels) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let n : ℤ := ⌊x⌋
  have hxl : (n : ℝ) ≤ x := Int.floor_le x
  have hxr : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
  have hleft : ContinuousOn (pastedFareyHeight levels)
      (Icc ((n : ℝ) - 1) (n : ℝ)) := by
    simpa only [Int.cast_sub, Int.cast_one, sub_add_cancel] using
      pastedFareyHeight_continuousOn_unit levels (n - 1)
  have hright := pastedFareyHeight_continuousOn_unit levels n
  have hboth := hleft.union_of_isClosed hright isClosed_Icc isClosed_Icc
  have hunion : Icc ((n : ℝ) - 1) (n : ℝ) ∪ Icc (n : ℝ) ((n : ℝ) + 1) =
      Icc ((n : ℝ) - 1) ((n : ℝ) + 1) :=
    Icc_union_Icc_eq_Icc (by linarith) (by linarith)
  rw [hunion] at hboth
  exact hboth.continuousAt (Icc_mem_nhds (by linarith) hxr)

theorem pastedFareyHeight_nonneg (levels : ℤ → ℕ) (x : ℝ) :
    0 ≤ pastedFareyHeight levels x := chainHeight_nonneg _ _

/-- Uniform height control on every selected integer interval. -/
theorem pastedFareyHeight_bound_on_unit (levels : ℤ → ℕ) (n : ℤ) {x : ℝ}
    (hx : x ∈ Icc (n : ℝ) ((n : ℝ) + 1)) :
    pastedFareyHeight levels x ≤ 1 / (2 * ((levels n + 1 : ℕ) : ℝ)) := by
  rw [pastedFareyHeight_eq_on_unit levels n hx]
  exact sternBrocot_chainHeight_bound (levels n) (x - n)

end

end ThreeOmittedValues
