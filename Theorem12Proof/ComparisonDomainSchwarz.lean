module

public import Theorem12Proof.HalfPlaneSchwarz
public import Theorem12Proof.Vendor.DirichletRiemannMapping
import Mathlib.Tactic

/-!
# Comparing normalized conformal maps without Green functions

The inverse-map argument below is adapted from the prior Apache-2.0
Neumann formalization, `RequestProject/RiemannMappingInterior.lean`,
commit `b37a190b8afc6efb128f204176d26deec8d88a8c`. The open mapping and
nonzero derivative facts are supplied by the attributed Dirichlet excerpt.
-/

@[expose] public section

open Complex Metric Filter Topology Set

namespace ThreeOmittedValues

theorem holomorphic_inverse_on_image {D : Set ℂ} (hD : IsOpen D)
    (hDc : IsPreconnected D) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D)
    (hinj : InjOn f D) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (f '' D) ∧ MapsTo g (f '' D) D ∧
      (∀ z ∈ D, g (f z) = z) ∧ ∀ w ∈ f '' D, f (g w) = w := by
  classical
  set g := Function.invFunOn f D with hg
  have hgmem : ∀ w ∈ f '' D, g w ∈ D ∧ f (g w) = w := fun w hw =>
    Function.invFunOn_pos hw
  have hgf : ∀ z ∈ D, g (f z) = z := fun z hz =>
    hinj (hgmem _ (mem_image_of_mem f hz)).1 hz (hgmem _ (mem_image_of_mem f hz)).2
  have hopen : IsOpen (f '' D) :=
    isOpen_image_of_injOn hD hDc hf hinj subset_rfl hD
  refine ⟨g, ?_, fun w hw => (hgmem w hw).1, hgf, fun w hw => (hgmem w hw).2⟩
  intro w hw
  have hwn : f '' D ∈ 𝓝 w := hopen.mem_nhds hw
  obtain ⟨hgw, hfgw⟩ := hgmem w hw
  have hcont : ContinuousAt g w := by
    rw [ContinuousAt, (nhds_basis_opens (g w)).tendsto_right_iff]
    rintro V ⟨hV, hVo⟩
    have hopen' : IsOpen (f '' (V ∩ D)) :=
      isOpen_image_of_injOn hD hDc hf hinj inter_subset_right (hVo.inter hD)
    have hmem : w ∈ f '' (V ∩ D) := ⟨g w, ⟨hV, hgw⟩, hfgw⟩
    filter_upwards [hopen'.mem_nhds hmem] with y hy
    obtain ⟨z, ⟨hzV, hzD⟩, rfl⟩ := hy
    rw [hgf z hzD]
    exact hzV
  have hfder : HasDerivAt f (deriv f (g w)) (g w) :=
    (hf.differentiableAt (hD.mem_nhds hgw)).hasDerivAt
  have hne := deriv_ne_zero_of_injOn hD hf hinj hgw
  have hev : ∀ᶠ y in 𝓝 w, f (g y) = y := by
    filter_upwards [hwn] with y hy using (hgmem y hy).2
  exact (hfder.of_local_left_inverse hcont hne hev).differentiableAt.differentiableWithinAt

/-- If `ψ` maps the half-plane into the image of a normalized conformal
map `Φ` and `ψ(i) = Φ(i)`, the `Φ`-preimage of `ψ(z)` has at least one
quarter of the Blaschke weight of `z`. -/
theorem normalized_comparison_domain_weight {Φ ψ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im})
    (hΦinj : InjOn Φ {z : ℂ | 0 < z.im})
    (hψ : DifferentiableOn ℂ ψ {z : ℂ | 0 < z.im})
    (hψimage : MapsTo ψ {z : ℂ | 0 < z.im} (Φ '' {z : ℂ | 0 < z.im}))
    (hcenter : ψ Complex.I = Φ Complex.I) :
    ∃ G : ℂ → ℂ,
      DifferentiableOn ℂ G (Φ '' {z : ℂ | 0 < z.im}) ∧
      MapsTo G (Φ '' {z : ℂ | 0 < z.im}) {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → G (Φ z) = z) ∧
      (∀ w ∈ Φ '' {z : ℂ | 0 < z.im}, Φ (G w) = w) ∧
      ∀ z : ℂ, 0 < z.im → blaschkeWeight z ≤ 4 * blaschkeWeight (G (ψ z)) := by
  let D : Set ℂ := {z : ℂ | 0 < z.im}
  have hD : IsOpen D := isOpen_lt continuous_const Complex.continuous_im
  have hDc : IsPreconnected D := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨G, hG, hGmaps, hGΦ, hΦG⟩ := holomorphic_inverse_on_image hD hDc hΦ hΦinj
  refine ⟨G, hG, hGmaps, hGΦ, hΦG, ?_⟩
  let H : ℂ → ℂ := G ∘ ψ
  have hHd : DifferentiableOn ℂ H D := hG.comp hψ hψimage
  have hHmaps : ∀ z : ℂ, 0 < z.im → 0 < (H z).im := by
    intro z hz
    exact hGmaps (hψimage hz)
  have hHfix : H Complex.I = Complex.I := by
    change G (ψ Complex.I) = Complex.I
    rw [hcenter]
    exact hGΦ Complex.I (by simp [D])
  intro z hz
  exact halfPlane_blaschkeWeight_schwarz hHd hHmaps hHfix hz

end ThreeOmittedValues
