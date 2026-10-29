/-
Adapted from the connected-fiber argument in
RequestProject/RiemannMappingCaratheodory.lean, the prior Apache-2.0
Neumann development at commit b37a190b8afc6efb128f204176d26deec8d88a8c.
The Lipschitz-domain chart is replaced by an explicit local connectedness
property of the image domain.
-/
module

public import Theorem12Proof.ClosedDiskExtension
import Mathlib.Tactic

/-!
# Connected fibres of a closed-disk extension

The local connectedness hypothesis below is a geometric condition on the
actual image domain, established for Farey domains in later modules.
-/

@[expose] public section

open Set Metric Filter
open scoped Topology

namespace ThreeOmittedValues

def ConnectedBoundaryNeighborhoods (Ω : Set ℂ) : Prop :=
  ∀ p ∈ frontier Ω, ∀ d : ℝ, 0 < d → ∃ B : Set ℂ,
    IsOpen B ∧ p ∈ B ∧ B ⊆ ball p d ∧ IsPreconnected (Ω ∩ B)

theorem diskExtension_boundary_fiber_connected {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ p : ℂ,
      p ∈ frontier (F '' ball (0 : ℂ) 1) ∧
        Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    (hlocal : ConnectedBoundaryNeighborhoods (F '' ball (0 : ℂ) 1))
    {p : ℂ} (hp : p ∈ frontier (F '' ball (0 : ℂ) 1)) :
    IsConnected (closedBall (0 : ℂ) 1 ∩ diskExtension F ⁻¹' {p}) := by
  let Ω := F '' ball (0 : ℂ) 1
  let G := diskExtension F
  let A := closedBall (0 : ℂ) 1 ∩ G ⁻¹' {p}
  have hGc : ContinuousOn G (closedBall (0 : ℂ) 1) := diskExtension_continuousOn hF hboundary
  have hEq : EqOn G F (ball (0 : ℂ) 1) := diskExtension_eqOn F hF
  have hAc : IsClosed A := hGc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hAk : IsCompact A :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hAc inter_subset_left
  have hAne : A.Nonempty := by
    have hpim : p ∈ G '' sphere (0 : ℂ) 1 := by
      rw [diskExtension_sphere_image hF hinj hboundary]
      exact hp
    obtain ⟨ζ, hζ, he⟩ := hpim
    exact ⟨ζ, sphere_subset_closedBall hζ, he⟩
  refine ⟨hAne, ?_⟩
  apply isPreconnected_iff_subset_of_disjoint_closed.mpr
  intro u v hu hv hAuv hAdisj
  have hKu : IsCompact (A ∩ u) := hAk.inter_right hu
  have hKv : IsCompact (A ∩ v) := hAk.inter_right hv
  have hKdisj : Disjoint (A ∩ u) (A ∩ v) := by
    apply Set.disjoint_left.mpr
    intro z hzu hzv
    have hz : z ∈ A ∩ (u ∩ v) := ⟨hzu.1, hzu.2, hzv.2⟩
    rw [hAdisj] at hz
    exact hz
  obtain ⟨U, V, hUo, hVo, hKuU, hKvV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact hKu hKv hKdisj
  have hAUV : A ⊆ U ∪ V := by
    intro z hz
    rcases hAuv hz with hzu | hzv
    · exact Or.inl (hKuU ⟨hz, hzu⟩)
    · exact Or.inr (hKvV ⟨hz, hzv⟩)
  let T := closedBall (0 : ℂ) 1 \ (U ∪ V)
  have hTk : IsCompact T := (isCompact_closedBall (0 : ℂ) 1).diff (hUo.union hVo)
  have hGTk : IsCompact (G '' T) := hTk.image_of_continuousOn (hGc.mono diff_subset)
  have hpnot : p ∉ G '' T := by
    rintro ⟨z, hz, he⟩
    exact hz.2 (hAUV ⟨hz.1, he⟩)
  obtain ⟨d, hd, hdball⟩ := Metric.isOpen_iff.mp hGTk.isClosed.isOpen_compl p hpnot
  obtain ⟨B, hBo, hpB, hBball, hBconn⟩ := hlocal p hp d hd
  obtain ⟨J, hJ, hJm, hJF, hFJ⟩ :=
    PolyaNeumann.RiemannInterior.exists_holomorphic_inverse isOpen_ball
      (convex_ball (0 : ℂ) 1).isPreconnected hF hinj
  let S := J '' (Ω ∩ B)
  have hSc : IsPreconnected S := hBconn.image J (hJ.continuousOn.mono inter_subset_left)
  have hSclosedDisk : S ⊆ closedBall (0 : ℂ) 1 := by
    rintro z ⟨w, hw, rfl⟩
    exact ball_subset_closedBall (hJm hw.1)
  have hSG : MapsTo G S B := by
    rintro z ⟨w, hw, rfl⟩
    rw [hEq (hJm hw.1), hFJ w hw.1]
    exact hw.2
  have hSUV : S ⊆ U ∪ V := by
    intro z hz
    by_contra hn
    have hzim : G z ∈ G '' T := ⟨z, ⟨hSclosedDisk hz, hn⟩, rfl⟩
    exact hdball (hBball (hSG hz)) hzim
  have hAcl : A ⊆ closure S := by
    intro ζ hζ
    have hζcl : ζ ∈ closure (ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)]
      exact hζ.1
    letI : NeBot (𝓝[ball (0 : ℂ) 1] ζ) := mem_closure_iff_nhdsWithin_neBot.mp hζcl
    have hlim : Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p) := by
      have ht := tendsto_extendFrom (diskExtension_exists_limit hF hboundary hζ.1)
      change Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 (G ζ)) at ht
      rw [show G ζ = p from hζ.2] at ht
      exact ht
    have heB := hlim.eventually (hBo.mem_nhds hpB)
    have heS : ∀ᶠ z in 𝓝[ball (0 : ℂ) 1] ζ, z ∈ S := by
      filter_upwards [self_mem_nhdsWithin, heB] with z hz hzB
      exact ⟨F z, ⟨mem_image_of_mem F hz, hzB⟩, hJF z hz⟩
    exact mem_closure_of_tendsto
      ((tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 ζ) (𝓝 ζ)).mono_left nhdsWithin_le_nhds) heS
  rcases hSc.subset_or_subset hUo hVo hUV hSUV with hSU | hSV
  · left
    have hcl : closure S ⊆ Vᶜ := closure_minimal (hSU.trans hUV.subset_compl_right) hVo.isClosed_compl
    intro z hz
    rcases hAuv hz with hzu | hzv
    · exact hzu
    · exact False.elim (hcl (hAcl hz) (hKvV ⟨hz, hzv⟩))
  · right
    have hcl : closure S ⊆ Uᶜ := closure_minimal (hSV.trans hUV.symm.subset_compl_right) hUo.isClosed_compl
    intro z hz
    rcases hAuv hz with hzu | hzv
    · exact False.elim (hcl (hAcl hz) (hKuU ⟨hz, hzu⟩))
    · exact hzv

end ThreeOmittedValues
