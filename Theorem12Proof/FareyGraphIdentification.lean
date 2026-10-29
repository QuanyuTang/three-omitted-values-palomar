module

public import Theorem12Proof.FareyBelowGraph
import Mathlib.Tactic

/-!
# Identification of the pasted graph with Farey semicircles

The global union consists of the integer translates of the finite
Stern–Brocot semicircle chains. Each finite chain has determinant-one
neighbors by `SternBrocot.lean`.
-/

@[expose] public section

open Set

namespace ThreeOmittedValues

noncomputable section

/-- All translated finite edge arcs used by the pasted height. -/
def globalFareyArcs (levels : ℤ → ℕ) : Set ℂ :=
  {z | ∃ n : ℤ, z - (n : ℂ) ∈ finiteChainArcs (levels n)}

/-- The pasted continuous graph consists exactly of those translated arcs. -/
theorem globalFareyArcs_eq_graph (levels : ℤ → ℕ) :
    globalFareyArcs levels = {z : ℂ | z.im = pastedFareyHeight levels z.re} := by
  ext z
  constructor
  · rintro ⟨n, hz⟩
    change z.im = pastedFareyHeight levels z.re
    rw [finiteChainArcs_eq_graph] at hz
    change 0 ≤ (z - (n : ℂ)).re ∧ (z - (n : ℂ)).re ≤ 1 ∧
      (z - (n : ℂ)).im = chainHeight (sternBrocotEdges (levels n)) (z - (n : ℂ)).re at hz
    simp only [Complex.sub_re, Complex.sub_im, Complex.intCast_re, Complex.intCast_im, sub_zero] at hz
    have hx : z.re ∈ Icc (n : ℝ) ((n : ℝ) + 1) := ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
    rw [pastedFareyHeight_eq_on_unit levels n hx]
    exact hz.2.2
  · intro hz
    let n : ℤ := ⌊z.re⌋
    have hx : z.re ∈ Icc (n : ℝ) ((n : ℝ) + 1) :=
      ⟨Int.floor_le z.re, (Int.lt_floor_add_one z.re).le⟩
    refine ⟨n, ?_⟩
    rw [finiteChainArcs_eq_graph]
    change 0 ≤ (z - (n : ℂ)).re ∧ (z - (n : ℂ)).re ≤ 1 ∧
      (z - (n : ℂ)).im = chainHeight (sternBrocotEdges (levels n)) (z - (n : ℂ)).re
    simp only [Complex.sub_re, Complex.sub_im, Complex.intCast_re, Complex.intCast_im, sub_zero]
    refine ⟨by linarith [hx.1], by linarith [hx.2], ?_⟩
    rw [← pastedFareyHeight_eq_on_unit levels n hx]
    exact hz

/-- Every integer is a vertex of the pasted boundary. -/
theorem pastedFareyHeight_int (levels : ℤ → ℕ) (n : ℤ) :
    pastedFareyHeight levels (n : ℝ) = 0 := by
  have hn : (n : ℝ) ∈ Icc (n : ℝ) ((n : ℝ) + 1) := ⟨le_rfl, by linarith⟩
  rw [pastedFareyHeight_eq_on_unit levels n hn]
  simpa using sternBrocot_chainHeight_eq_zero_outside (levels n) (x := 0) (Or.inl le_rfl)

/-- Every listed finite-chain endpoint lies on the real axis of the graph. -/
theorem sternBrocot_chainHeight_eq_zero_at_endpoint (n : ℕ) {v : RationalEndpoint}
    (hv : HasEndpoint (sternBrocotEdges n) v) :
    chainHeight (sternBrocotEdges n) (endpointCoordinate v) = 0 := by
  obtain ⟨e, he, hl | hr⟩ := hv
  · rw [← hl, sternBrocot_chainHeight_eq_edge n he le_rfl (sternBrocotEdges_strict n he).le]
    exact edgeHeight_eq_zero_of_le_left e (sternBrocotEdges_strict n he).le le_rfl
  · rw [← hr, sternBrocot_chainHeight_eq_edge n he (sternBrocotEdges_strict n he).le le_rfl]
    exact edgeHeight_eq_zero_of_right_le e (sternBrocotEdges_strict n he).le le_rfl

/-- Every translated midpoint is a boundary vertex when each chosen depth
is positive. -/
theorem pastedFareyHeight_half_int (levels : ℤ → ℕ) (n : ℤ) (hn : 1 ≤ levels n) :
    pastedFareyHeight levels ((n : ℝ) + 1 / 2) = 0 := by
  have hx : (n : ℝ) + 1 / 2 ∈ Icc (n : ℝ) ((n : ℝ) + 1) := by constructor <;> linarith
  rw [pastedFareyHeight_eq_on_unit levels n hx]
  have hsub : (n : ℝ) + 1 / 2 - n = 1 / 2 := by ring
  rw [hsub]
  cases hlevel : levels n with
  | zero => omega
  | succ k =>
      have hv := sternBrocot_chainHeight_eq_zero_at_endpoint (k + 1)
        (sternBrocotEdges_has_half k)
      simpa [hlevel, endpointCoordinate] using hv

end

end ThreeOmittedValues
