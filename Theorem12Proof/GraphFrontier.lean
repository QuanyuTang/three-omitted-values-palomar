module

public import Theorem12Proof.GraphTopology
public import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Tactic

/-!
# Frontier of a continuous graph domain

Vertical shear carries the domain above a graph to the upper half-plane and
carries the graph itself to the real axis.
-/

@[expose] public section

open Complex Set

namespace ThreeOmittedValues

theorem frontier_upperGraphDomain {h : ℝ → ℝ} (hh : Continuous h) :
    frontier (upperGraphDomain h) = Set.range (graphMap h) := by
  let e := graphShear h hh
  have himage := e.image_frontier (upperGraphDomain h)
  rw [graphShear_image_upperGraphDomain hh, Complex.frontier_setOfPred_lt_im] at himage
  have him (z : ℂ) : (e z).im = z.im - h z.re := by
    simp [e, graphShear]
  rw [graphMap_range]
  ext z
  constructor
  · intro hz
    have hz' : e z ∈ {w : ℂ | w.im = 0} := by
      rw [← himage]
      exact ⟨z, hz, rfl⟩
    change (e z).im = 0 at hz'
    rw [him] at hz'
    change z.im = h z.re
    linarith
  · intro hz
    change z.im = h z.re at hz
    have hz' : e z ∈ e '' frontier (upperGraphDomain h) := by
      rw [himage]
      change (e z).im = 0
      rw [him, hz, sub_self]
    obtain ⟨w, hw, hwz⟩ := hz'
    have heq : w = z := e.injective hwz
    simpa only [heq] using hw

end ThreeOmittedValues
