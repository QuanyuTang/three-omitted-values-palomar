/-
Adapted from RequestProject/RiemannMappingCaratheodory.lean in the prior
Apache-2.0 Neumann development at commit b37a190b8afc6efb128f204176d26deec8d88a8c.
The image-domain local connectedness condition is explicit.
-/
module

public import Theorem12Proof.DiskFiberConnected
public import Theorem12Proof.Vendor.BoundaryUniqueness
import Mathlib.Tactic

/-!
# Closed-disk injectivity from locally connected image neighborhoods

The boundary injectivity conclusion is proved, not assumed. The geometric
neighborhood condition still has to be verified for the Farey domain.
-/

@[expose] public section

open Set Metric Filter Complex
open scoped Topology

namespace ThreeOmittedValues

theorem diskExtension_mem_image_iff {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ p : ℂ,
      p ∈ frontier (F '' ball (0 : ℂ) 1) ∧
        Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    diskExtension F z ∈ F '' ball (0 : ℂ) 1 ↔ z ∈ ball (0 : ℂ) 1 := by
  have hopen : IsOpen (F '' ball (0 : ℂ) 1) :=
    PolyaNeumann.RiemannInterior.isOpen_image_of_injOn isOpen_ball
      (convex_ball (0 : ℂ) 1).isPreconnected hF hinj Subset.rfl isOpen_ball
  constructor
  · intro hzin
    have hn : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    rcases eq_or_lt_of_le hn with hn | hn
    · have hfront := diskExtension_mem_frontier hboundary hn
      rw [hopen.frontier_eq] at hfront
      exact False.elim (hfront.2 hzin)
    · exact mem_ball_zero_iff.mpr hn
  · intro hzD
    rw [diskExtension_eqOn F hF hzD]
    exact mem_image_of_mem F hzD

theorem diskExtension_eq_of_eq_of_mem_disk {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ p : ℂ,
      p ∈ frontier (F '' ball (0 : ℂ) 1) ∧
        Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ closedBall (0 : ℂ) 1)
    (he : diskExtension F z = diskExtension F w) : z = w := by
  have hzΩ : diskExtension F z ∈ F '' ball (0 : ℂ) 1 :=
    (diskExtension_mem_image_iff hF hinj hboundary (ball_subset_closedBall hz)).mpr hz
  have hwD : w ∈ ball (0 : ℂ) 1 :=
    (diskExtension_mem_image_iff hF hinj hboundary hw).mp (he ▸ hzΩ)
  exact hinj hz hwD (by
    rw [diskExtension_eqOn F hF hz, diskExtension_eqOn F hF hwD] at he
    exact he)

theorem diskExtension_injOn_of_connected_neighborhoods {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ p : ℂ,
      p ∈ frontier (F '' ball (0 : ℂ) 1) ∧
        Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    (hlocal : ConnectedBoundaryNeighborhoods (F '' ball (0 : ℂ) 1)) :
    InjOn (diskExtension F) (closedBall (0 : ℂ) 1) := by
  let Ω := F '' ball (0 : ℂ) 1
  let G := diskExtension F
  have hopen : IsOpen Ω :=
    PolyaNeumann.RiemannInterior.isOpen_image_of_injOn isOpen_ball
      (convex_ball (0 : ℂ) 1).isPreconnected hF hinj Subset.rfl isOpen_ball
  have hGc : ContinuousOn G (closedBall (0 : ℂ) 1) := diskExtension_continuousOn hF hboundary
  have hEq : EqOn G F (ball (0 : ℂ) 1) := diskExtension_eqOn F hF
  have hGhol : DifferentiableOn ℂ G (ball (0 : ℂ) 1) := hF.congr (fun z hz => hEq hz)
  have hzeroD : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self zero_lt_one
  have hhalfD : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    norm_num
  have hnonconst (p : ℂ) : ¬ EqOn G (fun _ => p) (ball (0 : ℂ) 1) := by
    intro he
    have hval : F 0 = F (1 / 2) :=
      (hEq hzeroD).symm.trans ((he hzeroD).trans ((he hhalfD).symm.trans (hEq hhalfD)))
    have hbad := hinj hzeroD hhalfD hval
    norm_num at hbad
  intro z hz w hw he
  by_cases hzD : z ∈ ball (0 : ℂ) 1
  · exact diskExtension_eq_of_eq_of_mem_disk hF hinj hboundary hzD hw he
  by_cases hwD : w ∈ ball (0 : ℂ) 1
  · exact (diskExtension_eq_of_eq_of_mem_disk hF hinj hboundary hwD hz he.symm).symm
  have hzn : ‖z‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hz)
    (le_of_not_gt fun hn => hzD (mem_ball_zero_iff.mpr hn))
  by_contra hzw
  let p := G z
  let A := closedBall (0 : ℂ) 1 ∩ G ⁻¹' {p}
  have hp : p ∈ frontier Ω := diskExtension_mem_frontier hboundary hzn
  have hAconn : IsConnected A := diskExtension_boundary_fiber_connected hF hinj hboundary hlocal hp
  have hzA : z ∈ A := ⟨hz, rfl⟩
  have hwA : w ∈ A := ⟨hw, he.symm⟩
  have hAs : A ⊆ sphere (0 : ℂ) 1 := by
    intro v hv
    have hvn : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp hv.1
    have hvD : v ∉ ball (0 : ℂ) 1 := by
      intro hvD
      have hpin : p ∈ Ω := by
        rw [← hv.2]
        exact (diskExtension_mem_image_iff hF hinj hboundary hv.1).mpr hvD
      rw [hopen.frontier_eq] at hp
      exact hp.2 hpin
    have hvone : ‖v‖ = 1 := le_antisymm hvn (le_of_not_gt fun hn => hvD (mem_ball_zero_iff.mpr hn))
    simpa only [mem_sphere, dist_zero_right] using hvone
  have hηex : ∃ η : ℂ, ‖η‖ = 1 ∧ η ∉ A := by
    by_contra hno
    push_neg at hno
    have hGp : DiffContOnCl ℂ (fun v => G v - p) (ball (0 : ℂ) 1) :=
      (DiffContOnCl.mk_ball hGhol hGc).sub_const p
    have hzero : EqOn (fun v => G v - p) 0 (ball (0 : ℂ) 1) :=
      PolyaNeumann.diffContOnCl_eq_zero_of_circle_patch (fun v => G v - p) hGp
        (by norm_num : ‖(1 : ℂ)‖ = 1) zero_lt_one (by
          intro v hvs _
          have hvA := hno v (by simpa only [mem_sphere, dist_zero_right] using hvs)
          exact sub_eq_zero.mpr hvA.2)
    exact hnonconst p (fun v hv => sub_eq_zero.mp (hzero hv))
  obtain ⟨η, hη, hηA⟩ := hηex
  obtain ⟨ζ, hζ, d, hd, hpatch⟩ :=
    PolyaNeumann.exists_circle_patch_subset_of_preconnected hAconn.2 hAs hη hηA hzA hwA hzw
  have hGp : DiffContOnCl ℂ (fun v => G v - p) (ball (0 : ℂ) 1) :=
    (DiffContOnCl.mk_ball hGhol hGc).sub_const p
  have hzero : EqOn (fun v => G v - p) 0 (ball (0 : ℂ) 1) :=
    PolyaNeumann.diffContOnCl_eq_zero_of_circle_patch (fun v => G v - p) hGp hζ hd
      (fun v hvs hvn => sub_eq_zero.mpr (hpatch v hvs hvn).2)
  exact hnonconst p (fun v hv => sub_eq_zero.mp (hzero hv))

theorem diskExtension_homeomorph_of_connected_neighborhoods {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ p : ℂ,
      p ∈ frontier (F '' ball (0 : ℂ) 1) ∧
        Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p))
    (hlocal : ConnectedBoundaryNeighborhoods (F '' ball (0 : ℂ) 1)) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure (F '' ball (0 : ℂ) 1),
      ∀ z : closedBall (0 : ℂ) 1, (e z : ℂ) = diskExtension F z := by
  let G := diskExtension F
  have hGc : ContinuousOn G (closedBall (0 : ℂ) 1) := diskExtension_continuousOn hF hboundary
  have hGinj : InjOn G (closedBall (0 : ℂ) 1) :=
    diskExtension_injOn_of_connected_neighborhoods hF hinj hboundary hlocal
  have hGim : G '' closedBall (0 : ℂ) 1 = closure (F '' ball (0 : ℂ) 1) :=
    diskExtension_closed_image hF hboundary
  let f : closedBall (0 : ℂ) 1 → closure (F '' ball (0 : ℂ) 1) := fun z =>
    ⟨G z, hGim ▸ mem_image_of_mem G z.property⟩
  have hfc : Continuous f := hGc.restrict.subtype_mk _
  have hfb : Function.Bijective f := by
    constructor
    · intro z w he
      apply Subtype.ext
      exact hGinj z.property w.property (congrArg Subtype.val he)
    · intro w
      have hw : (w : ℂ) ∈ G '' closedBall (0 : ℂ) 1 := hGim.symm ▸ w.property
      obtain ⟨z, hz, hze⟩ := hw
      exact ⟨⟨z, hz⟩, Subtype.ext hze⟩
  letI : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  let e : closedBall (0 : ℂ) 1 ≃ closure (F '' ball (0 : ℂ) 1) := Equiv.ofBijective f hfb
  have hec : Continuous e := hfc
  exact ⟨hec.homeoOfEquivCompactToT2, fun _ => rfl⟩

end ThreeOmittedValues
