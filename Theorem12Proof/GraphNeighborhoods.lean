module

public import Theorem12Proof.GraphTopology
public import Theorem12Proof.DiskFiberConnected
import Mathlib.Tactic

/-!
# Connected local neighborhoods above a continuous graph

Vertical shear turns the intersection with each sufficiently small shear
ball into an intersection of the upper half-plane and a Euclidean ball.
-/

@[expose] public section

open Complex Metric Set Filter
open scoped Topology

namespace ThreeOmittedValues

theorem upperGraphDomain_connectedBoundaryNeighborhoods {h : ℝ → ℝ} (hh : Continuous h) :
    ConnectedBoundaryNeighborhoods (upperGraphDomain h) := by
  intro p hp d hd
  let e := graphShear h hh
  have hnear : e.symm ⁻¹' ball p d ∈ 𝓝 (e p) := by
    have hcont : ContinuousAt e.symm (e p) := e.symm.continuous.continuousAt
    apply hcont
    simpa only [Homeomorph.symm_apply_apply] using ball_mem_nhds p hd
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  let B := e ⁻¹' ball (e p) r
  have hBo : IsOpen B := isOpen_ball.preimage e.continuous
  have hpB : p ∈ B := mem_ball_self hr
  have hBsub : B ⊆ ball p d := by
    intro z hz
    have hz' : e.symm (e z) ∈ ball p d := hrsub hz
    simpa only [Homeomorph.symm_apply_apply] using hz'
  let H : Set ℂ := {z | 0 < z.im}
  have hΩw (w : ℂ) : e.symm w ∈ upperGraphDomain h ↔ w ∈ H := by
    constructor
    · intro hw
      have him : w ∈ e '' upperGraphDomain h := ⟨e.symm w, hw, e.apply_symm_apply w⟩
      rw [graphShear_image_upperGraphDomain hh] at him
      exact him
    · intro hw
      have him : w ∈ e '' upperGraphDomain h := by
        rw [graphShear_image_upperGraphDomain hh]
        exact hw
      obtain ⟨z, hz, heq⟩ := him
      have hz' : e.symm w = z := by rw [← heq, Homeomorph.symm_apply_apply]
      simpa only [hz'] using hz
  have heq : e.symm '' (H ∩ ball (e p) r) = upperGraphDomain h ∩ B := by
    ext z
    constructor
    · rintro ⟨w, ⟨hwH, hwB⟩, rfl⟩
      refine ⟨(hΩw w).2 hwH, ?_⟩
      change e (e.symm w) ∈ ball (e p) r
      simpa only [Homeomorph.apply_symm_apply] using hwB
    · rintro ⟨hzΩ, hzB⟩
      refine ⟨e z, ⟨(hΩw (e z)).1 ?_, hzB⟩, e.symm_apply_apply z⟩
      simpa only [Homeomorph.symm_apply_apply] using hzΩ
  have hconn : IsPreconnected (upperGraphDomain h ∩ B) := by
    rw [← heq]
    exact ((convex_halfSpace_im_gt 0).inter (convex_ball (e p) r)).isPreconnected.image
      e.symm e.symm.continuous.continuousOn
  exact ⟨B, hBo, hpB, hBsub, hconn⟩

end ThreeOmittedValues
