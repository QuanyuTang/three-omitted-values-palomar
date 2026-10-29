module

public import Theorem12Proof.CompactGraphFrontier
public import Theorem12Proof.GraphNeighborhoods
public import Theorem12Proof.GraphExteriorConnected
import Mathlib.Tactic

/-!
# Connected boundary neighborhoods after compactification

Finite boundary points are handled by the Cayley partial homeomorphism.
At infinity, the inverse image of a small ball is an exterior graph
domain, which remains connected.
-/

@[expose] public section

open Complex Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem norm_halfPlaneToCayley_sub_one {z : ℂ} (hz : z + Complex.I ≠ 0) :
    ‖halfPlaneToCayley z - 1‖ = 2 / ‖z + Complex.I‖ := by
  have heq : halfPlaneToCayley z - 1 = (-2 * Complex.I) / (z + Complex.I) := by
    unfold halfPlaneToCayley
    field_simp
    ring
  rw [heq]
  simp

theorem cayley_frontier_iff_of_ne_one {h : ℝ → ℝ} (h0 : ∀ x, 0 ≤ h x)
    {p : ℂ} (hp1 : p ≠ 1) :
    p ∈ frontier (halfPlaneToCayley '' upperGraphDomain h) ↔
      cayleyToHalfPlane p ∈ frontier (upperGraphDomain h) := by
  have hfront := cayleyPartialHomeomorph.symm.preimage_frontier (upperGraphDomain h)
  change {w : ℂ | w ≠ 1} ∩ cayleyToHalfPlane ⁻¹' frontier (upperGraphDomain h) =
    {w : ℂ | w ≠ 1} ∩ frontier (cayleyToHalfPlane ⁻¹' upperGraphDomain h) at hfront
  rw [cayley_preimage_upperGraphDomain h0] at hfront
  have h := Set.ext_iff.mp hfront p
  simp only [mem_inter_iff, mem_setOf_eq, mem_preimage] at h
  constructor
  · intro hp
    exact (h.mpr ⟨hp1, hp⟩).2
  · intro hp
    exact (h.mp ⟨hp1, hp⟩).2

theorem compactGraph_neighborhood_connected_at_one {h : ℝ → ℝ}
    (hh : Continuous h) (h0 : ∀ x, 0 ≤ h x) {d : ℝ} (hd : 0 < d) :
    IsPreconnected ((halfPlaneToCayley '' upperGraphDomain h) ∩ ball (1 : ℂ) d) := by
  have hequiv (z : ℂ) (hz : z ∈ upperGraphDomain h) :
      halfPlaneToCayley z ∈ ball (1 : ℂ) d ↔ 2 / d < ‖z + Complex.I‖ := by
    have hzpos : 0 < z.im := (h0 z.re).trans_lt hz
    have hden : z + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos hzpos
    have hnorm : 0 < ‖z + Complex.I‖ := norm_pos_iff.mpr hden
    rw [mem_ball, dist_eq_norm, norm_halfPlaneToCayley_sub_one hden]
    constructor
    · intro ht
      apply (div_lt_iff₀ hd).2
      have ht' := (div_lt_iff₀ hnorm).1 ht
      nlinarith
    · intro ht
      apply (div_lt_iff₀ hnorm).2
      have ht' := (div_lt_iff₀ hd).1 ht
      nlinarith
  have himage : (halfPlaneToCayley '' upperGraphDomain h) ∩ ball (1 : ℂ) d =
      halfPlaneToCayley '' (upperGraphDomain h ∩ {z : ℂ | 2 / d < ‖z + Complex.I‖}) := by
    ext w
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hw⟩
      exact ⟨z, ⟨hz, (hequiv z hz).1 hw⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzt⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, (hequiv z hz).2 hzt⟩
  rw [himage]
  have hconn := upperGraphDomain_inter_exterior_preconnected hh h0
    (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 2) hd))
  have hcont : ContinuousOn halfPlaneToCayley
      (upperGraphDomain h ∩ {z : ℂ | 2 / d < ‖z + Complex.I‖}) := by
    apply cayleyPartialHomeomorph.continuousOn.mono
    intro z hz
    change z + Complex.I ≠ 0
    exact add_I_ne_zero_of_im_pos ((h0 z.re).trans_lt hz.1)
  exact hconn.image halfPlaneToCayley hcont

theorem compactGraph_neighborhood_connected_away_from_one {h : ℝ → ℝ}
    (hh : Continuous h) (h0 : ∀ x, 0 ≤ h x) {p : ℂ}
    (hp : p ∈ frontier (halfPlaneToCayley '' upperGraphDomain h)) (hp1 : p ≠ 1)
    {d : ℝ} (hd : 0 < d) :
    ∃ B : Set ℂ, IsOpen B ∧ p ∈ B ∧ B ⊆ ball p d ∧
      IsPreconnected ((halfPlaneToCayley '' upperGraphDomain h) ∩ B) := by
  let z := cayleyToHalfPlane p
  have hzfront : z ∈ frontier (upperGraphDomain h) := (cayley_frontier_iff_of_ne_one h0 hp1).1 hp
  have hzsrc : z + Complex.I ≠ 0 := cayleyToHalfPlane_add_I_ne_zero hp1
  have hzp : halfPlaneToCayley z = p := halfPlaneToCayley_cayleyToHalfPlane_of_ne_one hp1
  have hc : ContinuousAt halfPlaneToCayley z := by
    unfold halfPlaneToCayley
    exact (continuousAt_id.sub continuousAt_const).div (continuousAt_id.add continuousAt_const) hzsrc
  have hnear : cayleyPartialHomeomorph.source ∩ (halfPlaneToCayley ⁻¹' ball p d) ∈ 𝓝 z := by
    apply inter_mem
    · exact cayleyPartialHomeomorph.open_source.mem_nhds hzsrc
    · apply hc
      simpa only [hzp] using ball_mem_nhds p hd
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨B, hBo, hzB, hBsub, hBconn⟩ :=
    upperGraphDomain_connectedBoundaryNeighborhoods hh z hzfront r hr
  have hBsrc : B ⊆ cayleyPartialHomeomorph.source := fun w hw => (hrsub (hBsub hw)).1
  have hBc : ∀ w ∈ B, halfPlaneToCayley w ∈ ball p d := fun w hw => (hrsub (hBsub hw)).2
  have hΩsrc : upperGraphDomain h ⊆ cayleyPartialHomeomorph.source := by
    intro w hw
    change w + Complex.I ≠ 0
    exact add_I_ne_zero_of_im_pos ((h0 w.re).trans_lt hw)
  let W := halfPlaneToCayley '' B
  have hWo : IsOpen W := cayleyPartialHomeomorph.isOpen_image_of_subset_source hBo hBsrc
  have hpW : p ∈ W := ⟨z, hzB, hzp⟩
  have hWsub : W ⊆ ball p d := by
    rintro _ ⟨w, hw, rfl⟩
    exact hBc w hw
  have heq : (halfPlaneToCayley '' upperGraphDomain h) ∩ W =
      halfPlaneToCayley '' (upperGraphDomain h ∩ B) := by
    ext w
    constructor
    · rintro ⟨⟨x, hx, hxw⟩, ⟨y, hy, hyw⟩⟩
      have hxne : x + Complex.I ≠ 0 := hΩsrc hx
      have hyne : y + Complex.I ≠ 0 := hBsrc hy
      have hxy : x = y := halfPlaneToCayley_injective_of_denominators hxne hyne (hxw.trans hyw.symm)
      subst y
      exact ⟨x, ⟨hx, hy⟩, hxw⟩
    · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, ⟨x, hy, rfl⟩⟩
  have hconn : IsPreconnected ((halfPlaneToCayley '' upperGraphDomain h) ∩ W) := by
    rw [heq]
    apply hBconn.image halfPlaneToCayley
    apply cayleyPartialHomeomorph.continuousOn.mono
    exact inter_subset_left.trans hΩsrc
  exact ⟨W, hWo, hpW, hWsub, hconn⟩

theorem compactGraphDomain_connectedBoundaryNeighborhoods {h : ℝ → ℝ}
    (hh : Continuous h) (h0 : ∀ x, 0 ≤ h x) :
    ConnectedBoundaryNeighborhoods (halfPlaneToCayley '' upperGraphDomain h) := by
  intro p hp d hd
  by_cases hp1 : p = 1
  · subst p
    exact ⟨ball 1 d, isOpen_ball, mem_ball_self hd, Subset.rfl,
      compactGraph_neighborhood_connected_at_one hh h0 hd⟩
  · exact compactGraph_neighborhood_connected_away_from_one hh h0 hp hp1 hd

end ThreeOmittedValues
