module

public import Theorem12Proof.CayleyPartialHomeomorph
public import Theorem12Proof.GraphFrontier
import Mathlib.Tactic

/-!
# Frontier of the compactified graph domain

The Cayley image of the domain above a nonnegative continuous graph has
frontier equal to the compactified graph, including its common point at
infinity.
-/

@[expose] public section

open Complex Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem cayley_preimage_upperGraphDomain {h : ℝ → ℝ} (h0 : ∀ x, 0 ≤ h x) :
    cayleyToHalfPlane ⁻¹' upperGraphDomain h = halfPlaneToCayley '' upperGraphDomain h := by
  ext w
  constructor
  · intro hwΩ
    by_cases hw : w = 1
    · subst w
      have ht : cayleyToHalfPlane 1 = 0 := by simp [cayleyToHalfPlane]
      change h (cayleyToHalfPlane 1).re < (cayleyToHalfPlane 1).im at hwΩ
      rw [ht] at hwΩ
      simp only [Complex.zero_re, Complex.zero_im] at hwΩ
      exact False.elim ((not_lt_of_ge (h0 0)) hwΩ)
    · exact ⟨cayleyToHalfPlane w, hwΩ, halfPlaneToCayley_cayleyToHalfPlane_of_ne_one hw⟩
  · rintro ⟨z, hz, rfl⟩
    have hzpos : 0 < z.im := (h0 z.re).trans_lt hz
    have hden : z + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos hzpos
    change cayleyToHalfPlane (halfPlaneToCayley z) ∈ upperGraphDomain h
    rw [cayleyToHalfPlane_halfPlaneToCayley_of_denominator hden]
    exact hz

theorem one_mem_frontier_compactGraphDomain {h : ℝ → ℝ} (h0 : ∀ x, 0 ≤ h x) :
    (1 : ℂ) ∈ frontier (halfPlaneToCayley '' upperGraphDomain h) := by
  let H : ℝ → ℝ := fun x => h x + 1
  have hH : ∀ x, 0 ≤ H x := fun x => by dsimp [H]; linarith [h0 x]
  have hlim : Tendsto (halfPlaneToCayley ∘ graphMap H) atTop (𝓝 1) :=
    compactGraph_tendsto_one hH tendsto_abs_atTop_atTop
  have hmem : ∀ x : ℝ, (halfPlaneToCayley ∘ graphMap H) x ∈
      halfPlaneToCayley '' upperGraphDomain h := by
    intro x
    refine ⟨graphMap H x, ?_, rfl⟩
    change h (graphMap H x).re < (graphMap H x).im
    simp only [graphMap_re, graphMap_im, H]
    linarith
  have hcl : (1 : ℂ) ∈ closure (halfPlaneToCayley '' upperGraphDomain h) :=
    mem_closure_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  have hnot : (1 : ℂ) ∉ halfPlaneToCayley '' upperGraphDomain h := by
    rintro ⟨z, hz, heq⟩
    have hzpos : 0 < z.im := (h0 z.re).trans_lt hz
    exact halfPlaneToCayley_ne_one_of_denominator (add_I_ne_zero_of_im_pos hzpos) heq
  exact ⟨hcl, fun hi => hnot (interior_subset hi)⟩

theorem frontier_compactGraphDomain {h : ℝ → ℝ} (hh : Continuous h) (h0 : ∀ x, 0 ≤ h x) :
    frontier (halfPlaneToCayley '' upperGraphDomain h) =
      insert 1 (Set.range (halfPlaneToCayley ∘ graphMap h)) := by
  let D : Set ℂ := halfPlaneToCayley '' upperGraphDomain h
  have hfront := cayleyPartialHomeomorph.symm.preimage_frontier (upperGraphDomain h)
  change {w : ℂ | w ≠ 1} ∩ cayleyToHalfPlane ⁻¹' frontier (upperGraphDomain h) =
    {w : ℂ | w ≠ 1} ∩ frontier (cayleyToHalfPlane ⁻¹' upperGraphDomain h) at hfront
  rw [cayley_preimage_upperGraphDomain h0] at hfront
  have hiff (w : ℂ) (hw : w ≠ 1) :
      w ∈ frontier D ↔ cayleyToHalfPlane w ∈ frontier (upperGraphDomain h) := by
    have h := Set.ext_iff.mp hfront w
    simp only [mem_inter_iff, mem_setOf_eq, mem_preimage] at h
    constructor
    · intro hwD
      exact (h.mpr ⟨hw, hwD⟩).2
    · intro hwΩ
      exact (h.mp ⟨hw, hwΩ⟩).2
  have h1 : (1 : ℂ) ∈ frontier D := one_mem_frontier_compactGraphDomain h0
  change frontier D = _
  ext w
  by_cases hw : w = 1
  · subst w
    simp [h1]
  · rw [hiff w hw, frontier_upperGraphDomain hh]
    simp only [mem_range, mem_insert_iff, hw, false_or, Function.comp_apply]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [hx]
      exact halfPlaneToCayley_cayleyToHalfPlane_of_ne_one hw
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [← hx]
      exact (cayleyToHalfPlane_halfPlaneToCayley_of_denominator (graph_denominator_ne h0 x)).symm

end ThreeOmittedValues
