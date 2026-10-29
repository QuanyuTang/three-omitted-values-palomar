module

public import Theorem12Proof.RequestProject.RiemannMappingBoundaryCrosscut
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Genuine arclength parametrization of conformal caps

The length is the integral of the actual cut-off angular derivative.
Its strict increase follows from the true subarc displacement estimate
and interior injectivity, including when the two physical endpoint
limits coincide. The intermediate value theorem and interval projection
construct a genuine global Lipschitz parametrization and its continuous
inverse parameter. No regularity at the two endpoint limits is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

/-- A proved length coordinate with the actual displacement inequality
gives a genuine Lipschitz parametrization. The inverse is constructed
from its strict order and the intermediate value theorem. -/
theorem exists_lipschitz_reparam_of_length {G : ℝ → ℂ} {ℓ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hℓc : ContinuousOn ℓ (Icc a b))
    (hℓs : StrictMonoOn ℓ (Icc a b)) (hℓa : ℓ a = 0)
    (hdom : ∀ θ ∈ Icc a b, ∀ τ ∈ Icc a b, θ ≤ τ →
      ‖G τ - G θ‖ ≤ ℓ τ - ℓ θ) :
    ∃ (τ : ℝ → ℝ) (H : ℝ → ℂ), Continuous τ ∧ LipschitzWith 1 H ∧
      (∀ u, τ u ∈ Icc a b) ∧
      (∀ u ∈ Icc 0 (ℓ b), ℓ (τ u) = u) ∧
      (∀ θ ∈ Icc a b, τ (ℓ θ) = θ) ∧
      (∀ u, H u = G (τ u)) ∧ H '' Icc 0 (ℓ b) = G '' Icc a b := by
  have hL : 0 < ℓ b := by
    rw [← hℓa]
    exact hℓs ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  let f : Icc a b → Icc 0 (ℓ b) := fun θ =>
    ⟨ℓ θ, ⟨by rw [← hℓa]; exact hℓs.monotoneOn ⟨le_rfl, hab.le⟩ θ.property θ.property.1,
      hℓs.monotoneOn θ.property ⟨hab.le, le_rfl⟩ θ.property.2⟩⟩
  have hfs : StrictMono f := fun θ ψ hθψ => hℓs θ.property ψ.property hθψ
  have hfo : Function.Surjective f := by
    intro u
    have hu : (u : ℝ) ∈ Icc (ℓ a) (ℓ b) := by simpa only [hℓa] using u.property
    obtain ⟨θ, hθ, heq⟩ := intermediate_value_Icc hab.le hℓc hu
    exact ⟨⟨θ, hθ⟩, Subtype.ext heq⟩
  let e : Icc a b ≃o Icc 0 (ℓ b) := StrictMono.orderIsoOfSurjective f hfs hfo
  let τ : ℝ → ℝ := fun u => (e.symm (projIcc 0 (ℓ b) hL.le u) : ℝ)
  let H : ℝ → ℂ := fun u => G (τ u)
  have hτc : Continuous τ := continuous_subtype_val.comp
    (e.symm.continuous.comp (LipschitzWith.projIcc hL.le).continuous)
  have hτmem (u : ℝ) : τ u ∈ Icc a b := (e.symm _).property
  have hτℓ (u : ℝ) : ℓ (τ u) = (projIcc 0 (ℓ b) hL.le u : ℝ) := by
    exact congrArg (fun x : Icc 0 (ℓ b) => (x : ℝ))
      (e.apply_symm_apply (projIcc 0 (ℓ b) hL.le u))
  have hτright (u : ℝ) (hu : u ∈ Icc 0 (ℓ b)) : ℓ (τ u) = u := by
    rw [hτℓ, projIcc_of_mem _ hu]
  have hτleft (θ : ℝ) (hθ : θ ∈ Icc a b) : τ (ℓ θ) = θ := by
    have hℓθ : ℓ θ ∈ Icc 0 (ℓ b) := (f ⟨θ, hθ⟩).property
    have hp : projIcc 0 (ℓ b) hL.le (ℓ θ) = e ⟨θ, hθ⟩ := by
      rw [projIcc_of_mem _ hℓθ]
      rfl
    change (e.symm (projIcc 0 (ℓ b) hL.le (ℓ θ)) : ℝ) = θ
    rw [hp, e.symm_apply_apply]
  have habs : ∀ θ ∈ Icc a b, ∀ ψ ∈ Icc a b,
      ‖G θ - G ψ‖ ≤ |ℓ θ - ℓ ψ| := by
    intro θ hθ ψ hψ
    rcases le_total θ ψ with h | h
    · have hm := hℓs.monotoneOn hθ hψ h
      rw [abs_of_nonpos (sub_nonpos.mpr hm), norm_sub_rev]
      have hd := hdom θ hθ ψ hψ h
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr (hℓs.monotoneOn hψ hθ h))]
      exact hdom ψ hψ θ hθ h
  have hH : LipschitzWith 1 H := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    have h := habs (τ u) (hτmem u) (τ v) (hτmem v)
    rw [hτℓ, hτℓ] at h
    have hc := (LipschitzWith.projIcc hL.le).dist_le_mul u v
    rw [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at hc
    simpa only [H, dist_eq_norm, NNReal.coe_one, one_mul, Real.dist_eq]
      using h.trans hc
  refine ⟨τ, H, hτc, hH, hτmem, hτright, hτleft, fun _ => rfl, ?_⟩
  ext z
  constructor
  · rintro ⟨u, _, rfl⟩
    exact ⟨τ u, hτmem u, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨ℓ θ, (f ⟨θ, hθ⟩).property, ?_⟩
    simp only [H, hτleft θ hθ]

/-- The actual angular arclength, with its prescribed starting point. -/
def riemannCapArcLength (F : ℂ → ℂ) (c : ℂ) (r a θ : ℝ) : ℝ :=
  ∫ s in a..θ, ‖riemannCapDerivative F c r s‖

theorem riemannCapArcLength_continuous (F : ℂ → ℂ) (c : ℂ) (r a : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi)) :
    Continuous (riemannCapArcLength F c r a) :=
  intervalIntegral.continuous_primitive
    (fun s t => (riemannCapDerivative_intervalIntegrable F c r hi s t).norm) a

theorem riemannCapArcLength_sub (F : ℂ → ℂ) (c : ℂ) (r a θ ψ : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi)) :
    riemannCapArcLength F c r a ψ - riemannCapArcLength F c r a θ =
      ∫ s in θ..ψ, ‖riemannCapDerivative F c r s‖ :=
  intervalIntegral.integral_interval_sub_left
    (riemannCapDerivative_intervalIntegrable F c r hi a ψ).norm
    (riemannCapDerivative_intervalIntegrable F c r hi a θ).norm

theorem riemannCapArcLength_monotone (F : ℂ → ℂ) (c : ℂ) (r a : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi)) :
    Monotone (riemannCapArcLength F c r a) := by
  intro θ ψ hθψ
  apply sub_nonneg.mp
  rw [riemannCapArcLength_sub F c r a θ ψ hi]
  exact intervalIntegral.integral_nonneg_of_forall hθψ (fun _ => norm_nonneg _)

/-- Actual interior injectivity prevents the genuine length from being
constant on any nontrivial subinterval, including the entire closed cap
when its two endpoint limits happen to agree. -/
theorem riemannCapArcLength_strictMonoOn (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (c : ℂ) {r a b : ℝ}
    (hr : r ≠ 0) (hwidth : b - a ≤ 2 * Real.pi)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (harc : MapsTo (circleMap c r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b)) :
    StrictMonoOn (riemannCapArcLength F c r a) (Icc a b) := by
  let ℓ := riemannCapArcLength F c r a
  have hm : Monotone ℓ := riemannCapArcLength_monotone F c r a hi
  have hGi : InjOn G (Ioo a b) := by
    intro θ hθ ψ hψ he
    apply injOn_circleMap_of_abs_sub_le' hr hwidth
      (Ioo_subset_Ico_self hθ) (Ioo_subset_Ico_self hψ)
    exact hinj (harc hθ) (harc hψ) ((hGeq hθ).symm.trans (he.trans (hGeq hψ)))
  intro θ hθ ψ hψ hθψ
  by_contra h
  have he : ℓ θ = ℓ ψ := le_antisymm (hm hθψ.le) (le_of_not_gt h)
  let v := (2 * θ + ψ) / 3
  let w := (θ + 2 * ψ) / 3
  have hvθ : θ < v := by dsimp [v]; linarith
  have hvw : v < w := by dsimp [v, w]; linarith
  have hwψ : w < ψ := by dsimp [w]; linarith
  have hv : v ∈ Ioo a b := ⟨hθ.1.trans_lt hvθ, (hvw.trans hwψ).trans_le hψ.2⟩
  have hw : w ∈ Ioo a b := ⟨hθ.1.trans_lt (hvθ.trans hvw), hwψ.trans_le hψ.2⟩
  have hd := riemannMapping_cap_extension_subarc_displacement F hF c r hi harc hGc hGeq
    (Ioo_subset_Icc_self hv) (Ioo_subset_Icc_self hw) hvw.le
  rw [← riemannCapArcLength_sub F c r a v w hi] at hd
  have hzero : ‖G w - G v‖ ≤ 0 := by
    have h1 := hm hvθ.le
    have h2 := hm hwψ.le
    change ℓ w - ℓ v ≥ ‖G w - G v‖ at hd
    linarith
  have hGwv := sub_eq_zero.mp (norm_le_zero_iff.mp hzero)
  have hwv := hGi hw hv hGwv
  exact hvw.ne hwv.symm

/-- Genuine cap arclength produces a continuous inverse parameter and
an actual global `1`-Lipschitz physical curve with exactly the same
closed image. No endpoint distinction is required. -/
theorem riemannMapping_cap_arclength_reparam (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (c : ℂ) {r a b : ℝ}
    (hr : r ≠ 0) (hab : a < b) (hwidth : b - a ≤ 2 * Real.pi)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (harc : MapsTo (circleMap c r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b)) :
    let ℓ := riemannCapArcLength F c r a
    ∃ (τ : ℝ → ℝ) (H : ℝ → ℂ), Continuous τ ∧ LipschitzWith 1 H ∧
      (∀ u, τ u ∈ Icc a b) ∧
      (∀ u ∈ Icc 0 (ℓ b), ℓ (τ u) = u) ∧
      (∀ θ ∈ Icc a b, τ (ℓ θ) = θ) ∧
      (∀ u, H u = G (τ u)) ∧ H '' Icc 0 (ℓ b) = G '' Icc a b := by
  refine exists_lipschitz_reparam_of_length hab
    (riemannCapArcLength_continuous F c r a hi).continuousOn
    (riemannCapArcLength_strictMonoOn F hF hinj c hr hwidth hi harc hGc hGeq)
    (by simp only [riemannCapArcLength, intervalIntegral.integral_same]) ?_
  intro θ hθ ψ hψ hθψ
  rw [riemannCapArcLength_sub F c r a θ ψ hi]
  exact riemannMapping_cap_extension_subarc_displacement F hF c r hi harc hGc hGeq
    hθ hψ hθψ

theorem riemannCapArcLength_le_full_length (F : ℂ → ℂ) (c : ℂ) {r a b : ℝ}
    (hab : a ≤ b) (hwidth : b ≤ a + 2 * Real.pi)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi)) :
    riemannCapArcLength F c r a b ≤
      ∫ s in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r s‖ := by
  let V := riemannCapDerivative F c r
  have hp : Function.Periodic (fun s => ‖V s‖) (2 * Real.pi) :=
    (riemannCapDerivative_periodic F c r).comp norm
  calc
    _ ≤ ∫ s in a..a + 2 * Real.pi, ‖V s‖ :=
      intervalIntegral.integral_mono_interval le_rfl hab hwidth
        (Eventually.of_forall fun _ => norm_nonneg _)
        (riemannCapDerivative_intervalIntegrable F c r hi a _).norm
    _ = ∫ s in (-Real.pi)..Real.pi, ‖V s‖ := by
      simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring]
        using hp.intervalIntegral_add_eq a (-Real.pi)
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        integral_Ioc_eq_integral_Ioo]

/-- The actual cap derivative is continuous at every genuinely interior
source parameter, even though no derivative is required at the two
endpoint limits. -/
theorem riemannCapDerivative_continuousAt_interior (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (c : ℂ) (r θ : ℝ)
    (hθ : circleMap c r θ ∈ ball (0 : ℂ) 1) :
    ContinuousAt (riemannCapDerivative F c r) θ := by
  have hc : ContinuousAt (fun t =>
      deriv F (circleMap c r t) * (circleMap 0 r t * Complex.I)) θ :=
    (((hF.deriv isOpen_ball).continuousOn.continuousAt
      (isOpen_ball.mem_nhds hθ)).comp (continuous_circleMap c r).continuousAt).mul
        ((continuous_circleMap 0 r).continuousAt.mul_const Complex.I)
  apply hc.congr
  filter_upwards [(continuous_circleMap c r).continuousAt.preimage_mem_nhds
    (isOpen_ball.mem_nhds hθ)] with t ht
  have htDisk : circleMap c r t ∈ ball (0 : ℂ) 1 := ht
  simp only [riemannCapDerivative, riemannInteriorDerivative, indicator_of_mem htDisk]

theorem riemannCapDerivative_ne_zero_interior (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (c : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ)
    (hθ : circleMap c r θ ∈ ball (0 : ℂ) 1) :
    riemannCapDerivative F c r θ ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_riemannCapDerivative F c hr.le θ]
  simp only [riemannInteriorDerivative, indicator_of_mem hθ]
  exact mul_pos hr (norm_pos_iff.mpr
    (RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball hF hinj hθ))

theorem riemannCapArcLength_hasDerivAt_interior (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (c : ℂ) (r a θ : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (hθ : circleMap c r θ ∈ ball (0 : ℂ) 1) :
    HasDerivAt (riemannCapArcLength F c r a) ‖riemannCapDerivative F c r θ‖ θ :=
  intervalIntegral.integral_hasDerivAt_right
    (riemannCapDerivative_intervalIntegrable F c r hi a θ).norm
    (riemannCapDerivative_measurable F c r).norm.aestronglyMeasurable.stronglyMeasurableAtFilter
    (riemannCapDerivative_continuousAt_interior F hF c r θ hθ).norm

/-- The actual continuous inverse parameter has the reciprocal speed
derivative at every interior length parameter. -/
theorem riemannMapping_cap_inverse_hasDerivAt (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (c : ℂ) {r a b : ℝ} (hr : 0 < r)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (harc : MapsTo (circleMap c r) (Ioo a b) (ball (0 : ℂ) 1))
    {τ : ℝ → ℝ} (hτc : Continuous τ) (hτm : MapsTo τ univ (Icc a b))
    (hτr : ∀ u ∈ Icc 0 (riemannCapArcLength F c r a b),
      riemannCapArcLength F c r a (τ u) = u)
    {u : ℝ} (hu : u ∈ Ioo 0 (riemannCapArcLength F c r a b)) :
    HasDerivAt τ ‖riemannCapDerivative F c r (τ u)‖⁻¹ u := by
  have htu : τ u ∈ Icc a b := hτm (mem_univ _)
  have htri : τ u ∈ Ioo a b := by
    constructor
    · apply lt_of_le_of_ne htu.1
      intro he
      have h := hτr u (Ioo_subset_Icc_self hu)
      rw [← he, riemannCapArcLength, intervalIntegral.integral_same] at h
      linarith [hu.1]
    · apply lt_of_le_of_ne htu.2
      intro he
      have h := hτr u (Ioo_subset_Icc_self hu)
      rw [he] at h
      linarith [hu.2]
  have hd := riemannCapArcLength_hasDerivAt_interior F hF c r a (τ u) hi (harc htri)
  have hn : ‖riemannCapDerivative F c r (τ u)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (riemannCapDerivative_ne_zero_interior F hF hinj c hr _ (harc htri))
  apply HasDerivAt.of_local_left_inverse hτc.continuousAt hd hn
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
  exact hτr v (Ioo_subset_Icc_self hv)

/-- Actual arclength normalization has the genuine unit tangent on the
interior cap. This follows from the constructed inverse identity and
the physical derivative; it is not a boundary regularity assumption. -/
theorem riemannMapping_cap_arclength_hasDerivAt (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (c : ℂ) {r a b : ℝ} (hr : 0 < r)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (harc : MapsTo (circleMap c r) (Ioo a b) (ball (0 : ℂ) 1))
    {G H : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b))
    {τ : ℝ → ℝ} (hτc : Continuous τ) (hτm : MapsTo τ univ (Icc a b))
    (hτr : ∀ u ∈ Icc 0 (riemannCapArcLength F c r a b),
      riemannCapArcLength F c r a (τ u) = u)
    (hH : ∀ u, H u = G (τ u))
    {u : ℝ} (hu : u ∈ Ioo 0 (riemannCapArcLength F c r a b)) :
    HasDerivAt H (‖riemannCapDerivative F c r (τ u)‖⁻¹ •
      riemannCapDerivative F c r (τ u)) u := by
  have htu : τ u ∈ Icc a b := hτm (mem_univ _)
  have htri : τ u ∈ Ioo a b := by
    constructor
    · apply lt_of_le_of_ne htu.1
      intro he
      have h := hτr u (Ioo_subset_Icc_self hu)
      rw [← he, riemannCapArcLength, intervalIntegral.integral_same] at h
      linarith [hu.1]
    · apply lt_of_le_of_ne htu.2
      intro he
      have h := hτr u (Ioo_subset_Icc_self hu)
      rw [he] at h
      linarith [hu.2]
  have hGd : HasDerivAt G (riemannCapDerivative F c r (τ u)) (τ u) := by
    apply (riemannCapDerivative_hasDerivAt F hF c r (τ u) (harc htri)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds htri] with θ hθ
    exact hGeq hθ
  exact (hGd.scomp u (riemannMapping_cap_inverse_hasDerivAt F hF hinj c hr hi harc
    hτc hτm hτr hu)).congr_of_eventuallyEq (Eventually.of_forall hH)

/-- Arbitrarily short genuine conformal caps admit actual global
Lipschitz arclength parametrizations, with finite physical frontier
endpoints. All length and inverse hypotheses are derived from the true
finite conformal energy and interior injectivity. -/
theorem riemannMapping_exists_small_lipschitz_cap (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r : ℝ) (G : ℝ → ℂ) (τ : ℝ → ℝ) (H : ℝ → ℂ),
      0 < r ∧ r < δ ∧ r < 1 ∧ Continuous G ∧ Continuous τ ∧ LipschitzWith 1 H ∧
      let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
      let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
      let ℓ := riemannCapArcLength F ζ r a
      IntegrableOn (riemannCapDerivative F ζ r) (Ioo (-Real.pi) Real.pi) ∧
      0 < ℓ b ∧ ℓ b < ε ∧
      EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b) ∧
      G a ∈ frontier (F '' ball (0 : ℂ) 1) ∧
      G b ∈ frontier (F '' ball (0 : ℂ) 1) ∧
      (∀ u, τ u ∈ Icc a b) ∧
      (∀ u ∈ Icc 0 (ℓ b), ℓ (τ u) = u) ∧
      (∀ θ ∈ Icc a b, τ (ℓ θ) = θ ∧ H (ℓ θ) = G θ) ∧
      (∀ u, H u = G (τ u)) ∧ H 0 = G a ∧ H (ℓ b) = G b ∧
      H '' Icc 0 (ℓ b) = G '' Icc a b ∧ InjOn H (Ico 0 (ℓ b)) := by
  obtain ⟨r, hr, hi, hlength⟩ := riemannMapping_exists_small_cap_length F hF hinj hb ζ
    (show 0 < min δ 1 from lt_min hδ zero_lt_one) hε
  have hrδ := hr.2.trans_le (min_le_left δ 1)
  have hr1 := hr.2.trans_le (min_le_right δ 1)
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  let ℓ := riemannCapArcLength F ζ r a
  obtain ⟨hab, hwidth, harc, hza, hzb⟩ := riemannCap_geometry hζ hr.1 hr1
  have hwidth' : b - a ≤ 2 * Real.pi := by linarith
  obtain ⟨G, hGc, hGeq, hGaLim, hGbLim⟩ :=
    riemannMapping_cap_continuous_extension F hF ζ r hi hab harc
  have hGa : G a ∈ frontier (F '' ball (0 : ℂ) 1) := by
    letI := left_nhdsWithin_Ioo_neBot hab
    exact riemannMapping_limit_mem_frontier F hF hinj hza
      (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact harc hθ)
      (((continuous_circleMap ζ r).tendsto a).mono_left nhdsWithin_le_nhds) hGaLim
  have hGb : G b ∈ frontier (F '' ball (0 : ℂ) 1) := by
    letI := right_nhdsWithin_Ioo_neBot hab
    exact riemannMapping_limit_mem_frontier F hF hinj hzb
      (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact harc hθ)
      (((continuous_circleMap ζ r).tendsto b).mono_left nhdsWithin_le_nhds) hGbLim
  have hℓs : StrictMonoOn ℓ (Icc a b) :=
    riemannCapArcLength_strictMonoOn F hF hinj ζ hr.1.ne' hwidth' hi harc hGc hGeq
  have hℓa : ℓ a = 0 := by simp only [ℓ, riemannCapArcLength, intervalIntegral.integral_same]
  have hL : 0 < ℓ b := by
    rw [← hℓa]
    exact hℓs ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  have hLε : ℓ b < ε :=
    (riemannCapArcLength_le_full_length F ζ hab.le hwidth hi).trans_lt hlength
  obtain ⟨τ, H, hτc, hHlip, hτm, hτr, hτl, hH, hHim⟩ :=
    riemannMapping_cap_arclength_reparam F hF hinj ζ hr.1.ne' hab hwidth' hi harc hGc hGeq
  have hτ0 : τ 0 = a := by
    have h := hτl a ⟨le_rfl, hab.le⟩
    change τ (ℓ a) = a at h
    simpa only [hℓa] using h
  have hτL : τ (ℓ b) = b := hτl b ⟨hab.le, le_rfl⟩
  have hH0 : H 0 = G a := (hH 0).trans (congrArg G hτ0)
  have hHL : H (ℓ b) = G b := (hH _).trans (congrArg G hτL)
  have hGi := riemannMapping_cap_injOn_Ico F hF hinj hr.1.ne' hwidth' harc hGeq hGa
  have hHi : InjOn H (Ico 0 (ℓ b)) := by
    intro u hu v hv heq
    have huc : u ∈ Icc 0 (ℓ b) := Ico_subset_Icc_self hu
    have hvc : v ∈ Icc 0 (ℓ b) := Ico_subset_Icc_self hv
    have hτi (s : ℝ) (hs : s ∈ Ico 0 (ℓ b)) : τ s ∈ Ico a b := by
      refine ⟨(hτm s).1, ?_⟩
      apply lt_of_le_of_ne (hτm s).2
      intro hsb
      have h := hτr s (Ico_subset_Icc_self hs)
      rw [hsb] at h
      linarith [hs.2]
    have hτuv : τ u = τ v := hGi (hτi u hu) (hτi v hv)
      ((hH u).symm.trans (heq.trans (hH v)))
    have hru := hτr u huc
    rw [hτuv] at hru
    exact hru.symm.trans (hτr v hvc)
  refine ⟨r, G, τ, H, hr.1, hrδ, hr1, hGc, hτc, hHlip, hi, hL, hLε,
    hGeq, hGa, hGb, hτm, hτr, ?_, hH, hH0, hHL, hHim, hHi⟩
  intro θ hθ
  exact ⟨hτl θ hθ, (hH _).trans (congrArg G (hτl θ hθ))⟩

end PolyaNeumann

end
