module

-- Local port: the cap argument only uses the minimal area-energy input.
public import Theorem12Proof.RequestProject.InteriorConformalEnergyMinimal
public import Theorem12Proof.RequestProject.GreenWinding
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Finite-energy circular caps of the interior Riemann map

The derivative is cut off to the **open** disk, where the actual map is
holomorphic. Translated polar integration and the nonintegrability of
`1/r` at zero give arbitrarily small circles whose portions in the disk
have arbitrarily small image length. The chosen radius is also a genuine
integrable angular slice, so no default-valued integral is used as a
substitute for finite length.

Integrating the actual derivative on any open circular arc in the disk
constructs its finite endpoint values. None of these statements assumes
or asserts a continuous extension of the Riemann map to the whole circle.
The Jordan crosscut separation argument needed to turn these cap estimates
into a full Carathéodory extension remains a separate geometric step. In
that step distinct frontier endpoints are joined by a short physical
boundary arc; coincident endpoints instead give a small closed loop.
Endpoint injectivity is not assumed before proving the boundary theorem.
-/

@[expose] public section

set_option autoImplicit false
-- Local port: allow the current Mathlib definitions to unfold during type checking.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

/-- The actual complex derivative, extended by zero outside its open
domain. Values of the original total function on the boundary are unused. -/
def riemannInteriorDerivative (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (ball (0 : ℂ) 1).indicator (deriv F) z

theorem riemannInteriorDerivative_measurable (F : ℂ → ℂ) :
    Measurable (riemannInteriorDerivative F) :=
  (measurable_deriv F).indicator measurableSet_ball

theorem riemannInteriorDerivative_sq_integrable (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    Integrable (fun z => ‖riemannInteriorDerivative F z‖ ^ 2) := by
  have h := (interiorConformal_deriv_sq_integrable F hF hinj hb).integrable_indicator
    measurableSet_ball
  refine h.congr (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · simp only [riemannInteriorDerivative, indicator_of_mem hz]
  · simp only [riemannInteriorDerivative, indicator_of_notMem hz, norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0)]

/-- The true angular derivative of `F ∘ circleMap c r` on its portions
inside the disk, and zero on the remaining portions. -/
def riemannCapDerivative (F : ℂ → ℂ) (c : ℂ) (r θ : ℝ) : ℂ :=
  riemannInteriorDerivative F (circleMap c r θ) * (circleMap 0 r θ * Complex.I)

theorem riemannCapDerivative_measurable (F : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Measurable (riemannCapDerivative F c r) := by
  exact ((riemannInteriorDerivative_measurable F).comp
    (continuous_circleMap c r).measurable).mul
      ((continuous_circleMap 0 r).measurable.mul_const Complex.I)

theorem norm_riemannCapDerivative (F : ℂ → ℂ) (c : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (θ : ℝ) :
    ‖riemannCapDerivative F c r θ‖ =
      r * ‖riemannInteriorDerivative F (circleMap c r θ)‖ := by
  simp only [riemannCapDerivative, norm_mul, norm_circleMap_zero,
    abs_of_nonneg hr, Complex.norm_I, mul_one, mul_comm]

theorem riemannCapDerivative_hasDerivAt (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (c : ℂ) (r θ : ℝ) (hθ : circleMap c r θ ∈ ball (0 : ℂ) 1) :
    HasDerivAt (fun t => F (circleMap c r t)) (riemannCapDerivative F c r θ) θ := by
  have hd := (hF.differentiableAt (isOpen_ball.mem_nhds hθ)).hasDerivAt
  have h := hd.comp θ (hasDerivAt_circleMap c r θ)
  simpa only [riemannCapDerivative, riemannInteriorDerivative,
    indicator_of_mem hθ] using! h

/-- Polar integration of an actual nonnegative L¹ density after a
translation. This supplies both finite slices and an integrable radial
energy density. -/
private theorem translated_polar_integrable {g : ℂ → ℝ}
    (hgm : Measurable g) (hg : Integrable g) (c : ℂ) :
    IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * g (c + Complex.polarCoord.symm p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
  have ht : Integrable (fun z : ℂ => g (c + z)) := hg.comp_add_left c
  have hm : Measurable (fun p : ℝ × ℝ =>
      p.1 * g (c + Complex.polarCoord.symm p)) :=
    measurable_fst.mul (hgm.comp (measurable_const.add measurable_complexPolarCoord_symm))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have heq :
      (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ‖p.1 * g (c + Complex.polarCoord.symm p)‖ₑ) =
      ∫⁻ z : ℂ, ‖g (c + z)‖ₑ := by
    rw [← Complex.lintegral_comp_polarCoord_symm]
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    change ‖p.1 * g (c + Complex.polarCoord.symm p)‖ₑ =
      ENNReal.ofReal p.1 • ‖g (c + Complex.polarCoord.symm p)‖ₑ
    rw [enorm_mul, Real.enorm_eq_ofReal hp.1.le]
    rfl
  rw [heq]
  exact ht.hasFiniteIntegral

/-- An integrable radial energy cannot be bounded below by `ε/r` at
almost every sufficiently small radius. A null exceptional set of bad
slices can be excluded simultaneously. -/
private theorem exists_small_radius_of_integrable {R : ℝ → ℝ}
    (hR : IntegrableOn R (Ioi (0 : ℝ))) {P : ℝ → Prop}
    (hP : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), P r)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r ∈ Ioo (0 : ℝ) δ, P r ∧ r * R r < ε := by
  by_contra hn
  have hge : ∀ r ∈ Ioo (0 : ℝ) δ, P r → ε ≤ r * R r := by
    intro r hr hp
    by_contra hh
    exact hn ⟨r, hr, hp, lt_of_not_ge hh⟩
  have hi : IntegrableOn (fun r : ℝ => ε * r⁻¹) (Ioo 0 δ) := by
    apply (hR.mono_set Ioo_subset_Ioi_self).mono'
      (measurable_const.mul measurable_inv).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hP] with r hr hp
    change ‖ε * r⁻¹‖ ≤ R r
    rw [Real.norm_of_nonneg (mul_nonneg hε.le (inv_nonneg.mpr hr.1.le))]
    simpa only [div_eq_mul_inv] using
      (div_le_iff₀ hr.1).2 (by simpa only [mul_comm] using hge r hr hp)
  have hinv : IntegrableOn (fun r : ℝ => r⁻¹) (Ioo 0 δ) := by
    have h := hi.const_mul ε⁻¹
    rw [IntegrableOn]
    simpa only [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] using! h
  have hp : IntegrableOn (fun r : ℝ => r ^ (-1 : ℝ)) (Ioo 0 δ) := by
    simpa only [Real.rpow_neg_one] using hinv
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).1 hp
  linarith

/-- Arbitrarily small radii have a genuinely integrable angular
derivative and arbitrarily small angular squared energy. -/
theorem riemannMapping_exists_small_cap_energy (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (c : ℂ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r ∈ Ioo (0 : ℝ) δ,
      IntegrableOn (fun θ =>
        ‖riemannInteriorDerivative F (circleMap c r θ)‖ ^ 2)
        (Ioo (-Real.pi) Real.pi) ∧
      r ^ 2 * (∫ θ in Ioo (-Real.pi) Real.pi,
        ‖riemannInteriorDerivative F (circleMap c r θ)‖ ^ 2) < ε := by
  let g : ℂ → ℝ := fun z => ‖riemannInteriorDerivative F z‖ ^ 2
  have hgp := translated_polar_integrable
    ((riemannInteriorDerivative_measurable F).norm.pow_const 2)
    (riemannInteriorDerivative_sq_integrable F hF hinj hb) c
  have heq : ∀ p : ℝ × ℝ,
      c + Complex.polarCoord.symm p = circleMap c p.1 p.2 := by
    intro p
    rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [heq] at hgp
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hgp
  let R : ℝ → ℝ := fun r => ∫ θ in Ioo (-Real.pi) Real.pi,
    r * g (circleMap c r θ)
  have hR : IntegrableOn R (Ioi (0 : ℝ)) := hgp.integral_prod_left
  have hslice : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      IntegrableOn (fun θ => g (circleMap c r θ)) (Ioo (-Real.pi) Real.pi) := by
    filter_upwards [hgp.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    have h := hr.const_mul r⁻¹
    have hrpos : 0 < r := hr0
    rw [IntegrableOn]
    simpa only [g, ← mul_assoc, inv_mul_cancel₀ hrpos.ne', one_mul] using! h
  obtain ⟨r, hr, hs, hsmall⟩ := exists_small_radius_of_integrable hR hslice hδ hε
  refine ⟨r, hr, hs, ?_⟩
  simpa only [R, integral_const_mul, ← mul_assoc, ← pow_two, g] using hsmall

/-- Finite angular squared energy gives genuine finite angular length. -/
private theorem riemannCapDerivative_integrable (F : ℂ → ℂ) (c : ℂ)
    {r : ℝ} (hr : 0 ≤ r)
    (hs : IntegrableOn (fun θ =>
      ‖riemannInteriorDerivative F (circleMap c r θ)‖ ^ 2)
      (Ioo (-Real.pi) Real.pi)) :
    IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi) := by
  have hsq : IntegrableOn (fun θ => ‖riemannCapDerivative F c r θ‖ ^ 2)
      (Ioo (-Real.pi) Real.pi) := by
    rw [IntegrableOn] at hs ⊢
    simpa only [norm_riemannCapDerivative F c hr, mul_pow] using! hs.const_mul (r ^ 2)
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  apply (hconst.add hsq).mono' (riemannCapDerivative_measurable F c r).aestronglyMeasurable
  exact Eventually.of_forall fun θ => by
    dsimp
    nlinarith [sq_nonneg (‖riemannCapDerivative F c r θ‖ - 1)]

/-- The Courant–Lebesgue length consequence for the actual map. The
integral includes exactly the portions of the circle lying in the open
disk; the derivative was proved to vanish on its other portions. -/
theorem riemannMapping_exists_small_cap_length (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (c : ℂ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r ∈ Ioo (0 : ℝ) δ,
      IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi) ∧
      (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖) < ε := by
  let a : ℝ := ε / (4 * Real.pi)
  have ha : 0 < a := div_pos hε (by positivity)
  obtain ⟨r, hr, hs, hsmall⟩ := riemannMapping_exists_small_cap_energy
    F hF hinj hb c hδ (show 0 < 2 * a * ε by positivity)
  have hi := riemannCapDerivative_integrable F c hr.1.le hs
  have hsq : IntegrableOn (fun θ => ‖riemannCapDerivative F c r θ‖ ^ 2)
      (Ioo (-Real.pi) Real.pi) := by
    rw [IntegrableOn] at hs ⊢
    simpa only [norm_riemannCapDerivative F c hr.1.le, mul_pow]
      using! hs.const_mul (r ^ 2)
  have hsqsmall : (∫ θ in Ioo (-Real.pi) Real.pi,
      ‖riemannCapDerivative F c r θ‖ ^ 2) < 2 * a * ε := by
    simpa only [norm_riemannCapDerivative F c hr.1.le, mul_pow,
      integral_const_mul] using hsmall
  have hconst : IntegrableOn (fun _ : ℝ => a) (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hpoint : ∀ θ, ‖riemannCapDerivative F c r θ‖ ≤
      a + ‖riemannCapDerivative F c r θ‖ ^ 2 / (4 * a) := by
    intro θ
    have h : (‖riemannCapDerivative F c r θ‖ - a) * (4 * a) ≤
        ‖riemannCapDerivative F c r θ‖ ^ 2 := by
      nlinarith [sq_nonneg (‖riemannCapDerivative F c r θ‖ - 2 * a)]
    have := (le_div_iff₀ (show 0 < 4 * a by positivity)).2 h
    linarith
  have hle := integral_mono hi.norm (hconst.add (hsq.div_const (4 * a))) hpoint
  change (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖) ≤
    ∫ θ in Ioo (-Real.pi) Real.pi, a + ‖riemannCapDerivative F c r θ‖ ^ 2 / (4 * a) at hle
  have hmeasure : (∫ θ in Ioo (-Real.pi) Real.pi, a) = 2 * Real.pi * a := by
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    simp only [smul_eq_mul]
    ring
  rw [integral_add hconst (hsq.div_const (4 * a)), hmeasure, integral_div] at hle
  have hdiv : (∫ θ in Ioo (-Real.pi) Real.pi,
      ‖riemannCapDerivative F c r θ‖ ^ 2) / (4 * a) < ε / 2 := by
    apply (div_lt_iff₀ (show 0 < 4 * a by positivity)).2
    nlinarith [hsqsmall]
  refine ⟨r, hr, hi, hle.trans_lt ?_⟩
  have hhalf : 2 * Real.pi * a = ε / 2 := by
    dsimp [a]
    field_simp [Real.pi_pos.ne']; ring
  rw [hhalf]
  linarith

theorem riemannCapDerivative_periodic (F : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Function.Periodic (riemannCapDerivative F c r) (2 * Real.pi) := by
  intro θ
  simp only [riemannCapDerivative, periodic_circleMap c r θ,
    periodic_circleMap 0 r θ]

/-- A good polar slice is integrable on every finite angular interval,
including intervals crossing the polar cut. -/
theorem riemannCapDerivative_intervalIntegrable (F : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (a b : ℝ) : IntervalIntegrable (riemannCapDerivative F c r) volume a b := by
  have hbase : IntervalIntegrable (riemannCapDerivative F c r) volume
      (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
      intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])]
    exact hi
  exact (riemannCapDerivative_periodic F c r).intervalIntegrable Real.two_pi_pos.ne' hbase a b

/-- On an actual open circular arc inside the disk, the cut-off
derivative is continuous at each parameter. Nothing is required of `F`
at either endpoint of the arc. -/
private theorem riemannCapDerivative_continuousAt (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (c : ℂ) (r θ : ℝ) (hθ : circleMap c r θ ∈ ball (0 : ℂ) 1) :
    ContinuousAt (riemannCapDerivative F c r) θ := by
  have hcont : ContinuousAt (fun t =>
      deriv F (circleMap c r t) * (circleMap 0 r t * Complex.I)) θ := by
    exact (((hF.deriv isOpen_ball).continuousOn.continuousAt
      (isOpen_ball.mem_nhds hθ)).comp (continuous_circleMap c r).continuousAt).mul
        ((continuous_circleMap 0 r).continuousAt.mul_const Complex.I)
  apply hcont.congr
  have hmem : ∀ᶠ t in 𝓝 θ, circleMap c r t ∈ ball (0 : ℂ) 1 :=
    (continuous_circleMap c r).continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds hθ)
  filter_upwards [hmem] with t ht
  simp only [riemannCapDerivative, riemannInteriorDerivative, indicator_of_mem ht]

/-- The actual image of every open circular arc has finite endpoint
limits at a good radius. The continuous function is explicitly obtained
by integrating the true angular derivative; no boundary value of the
original total function is used. -/
theorem riemannMapping_cap_continuous_extension (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (c : ℂ) (r : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    {a b : ℝ} (hab : a < b)
    (harc : MapsTo (circleMap c r) (Ioo a b) (ball (0 : ℂ) 1)) :
    ∃ G : ℝ → ℂ, Continuous G ∧
      EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b) ∧
      Tendsto (fun θ => F (circleMap c r θ)) (𝓝[Ioo a b] a) (𝓝 (G a)) ∧
      Tendsto (fun θ => F (circleMap c r θ)) (𝓝[Ioo a b] b) (𝓝 (G b)) := by
  let t : ℝ := (a + b) / 2
  have ht : t ∈ Ioo a b := by dsimp [t]; constructor <;> linarith
  let V : ℝ → ℂ := riemannCapDerivative F c r
  have hVi : ∀ s u : ℝ, IntervalIntegrable V volume s u :=
    riemannCapDerivative_intervalIntegrable F c r hi
  let G : ℝ → ℂ := fun θ => F (circleMap c r t) + ∫ s in t..θ, V s
  have hGc : Continuous G := continuous_const.add
    (intervalIntegral.continuous_primitive hVi t)
  have hGd : ∀ θ ∈ Ioo a b, HasDerivAt G (V θ) θ := by
    intro θ hθ
    have hd := intervalIntegral.integral_hasDerivAt_right (hVi t θ)
      (riemannCapDerivative_measurable F c r).aestronglyMeasurable.stronglyMeasurableAtFilter
      (riemannCapDerivative_continuousAt F hF c r θ (harc hθ))
    simpa only [G, zero_add] using hd.const_add (F (circleMap c r t))
  have hfd : ∀ θ ∈ Ioo a b,
      HasDerivAt (fun s => F (circleMap c r s)) (V θ) θ :=
    fun θ hθ => riemannCapDerivative_hasDerivAt F hF c r θ (harc hθ)
  have heq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo a b).isPreconnected
      (fun θ hθ => (hGd θ hθ).differentiableAt.differentiableWithinAt)
      (fun θ hθ => (hfd θ hθ).differentiableAt.differentiableWithinAt)
      (fun θ hθ => by rw [(hGd θ hθ).deriv, (hfd θ hθ).deriv]) ht
    simp only [G, intervalIntegral.integral_same, add_zero]
  refine ⟨G, hGc, heq, ?_, ?_⟩
  · refine ((hGc.tendsto a).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact heq hθ
  · refine ((hGc.tendsto b).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact heq hθ

/-- The exact subarc length bound, including endpoint parameters. This
also supplies the genuine arclength domination needed to reparametrize
the cap image by a Lipschitz curve. -/
theorem riemannMapping_cap_extension_subarc_displacement (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (c : ℂ) (r : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    {a b : ℝ}
    (harc : MapsTo (circleMap c r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b))
    {θ τ : ℝ} (hθ : θ ∈ Icc a b) (hτ : τ ∈ Icc a b) (hθτ : θ ≤ τ) :
    ‖G τ - G θ‖ ≤ ∫ s in θ..τ, ‖riemannCapDerivative F c r s‖ := by
  have hsub : Ioo θ τ ⊆ Ioo a b := by
    intro s hs
    exact ⟨hθ.1.trans_lt hs.1, hs.2.trans_le hτ.2⟩
  have hGd : ∀ s ∈ Ioo a b, HasDerivAt G (riemannCapDerivative F c r s) s := by
    intro s hs
    apply (riemannCapDerivative_hasDerivAt F hF c r s (harc hs)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact hGeq hu
  apply norm_sub_le_integral_of_norm_deriv_le_of_le hθτ hGc.continuousOn
    (fun s hs => (hGd s (hsub hs)).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall fun s hs => ?_)
    (riemannCapDerivative_intervalIntegrable F c r hi θ τ).norm
  rw [(hGd s (hsub hs)).deriv]

/-- The displacement of the continuous cap image, including its newly
constructed endpoints, is bounded by the true length of the good slice. -/
theorem riemannMapping_cap_extension_displacement (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (c : ℂ) (r : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    {a b : ℝ} (_hab : a < b) (hwidth : b ≤ a + 2 * Real.pi)
    (harc : MapsTo (circleMap c r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b)) :
    ∀ θ ∈ Icc a b, ∀ τ ∈ Icc a b,
      ‖G θ - G τ‖ ≤
        ∫ s in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r s‖ := by
  let V : ℝ → ℂ := riemannCapDerivative F c r
  have hVi : ∀ s u : ℝ, IntervalIntegrable V volume s u :=
    riemannCapDerivative_intervalIntegrable F c r hi
  have hperiod : Function.Periodic (fun s => ‖V s‖) (2 * Real.pi) :=
    (riemannCapDerivative_periodic F c r).comp norm
  have hfull : (∫ s in a..a + 2 * Real.pi, ‖V s‖) =
      ∫ s in Ioo (-Real.pi) Real.pi, ‖V s‖ := by
    calc
      _ = ∫ s in (-Real.pi)..Real.pi, ‖V s‖ := by
        simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring]
          using hperiod.intervalIntegral_add_eq a (-Real.pi)
      _ = _ := by
        rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
          integral_Ioc_eq_integral_Ioo]
  have hordered : ∀ θ ∈ Icc a b, ∀ τ ∈ Icc a b, θ ≤ τ →
      ‖G τ - G θ‖ ≤ ∫ s in Ioo (-Real.pi) Real.pi, ‖V s‖ := by
    intro θ hθ τ hτ hθτ
    calc
      ‖G τ - G θ‖ ≤ ∫ s in θ..τ, ‖V s‖ :=
        riemannMapping_cap_extension_subarc_displacement F hF c r hi harc hGc hGeq hθ hτ hθτ
      _ ≤ ∫ s in a..a + 2 * Real.pi, ‖V s‖ :=
        intervalIntegral.integral_mono_interval hθ.1 hθτ (hτ.2.trans hwidth)
          (Eventually.of_forall fun _ => norm_nonneg _) (hVi a _).norm
      _ = _ := hfull
  intro θ hθ τ hτ
  rcases le_total θ τ with h | h
  · rw [norm_sub_rev]
    exact hordered θ hθ τ hτ h
  · exact hordered τ hτ θ hθ h

/-- A finite image limit at a boundary source point belongs to the
physical frontier. The genuine holomorphic interior inverse rules out
an interior image limit. -/
theorem riemannMapping_limit_mem_frontier {A : Type*} {l : Filter A} [NeBot l]
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    {z : A → ℂ} {ζ w : ℂ} (hζ : ‖ζ‖ = 1)
    (hzin : ∀ᶠ x in l, z x ∈ ball (0 : ℂ) 1)
    (hz : Tendsto z l (𝓝 ζ)) (hw : Tendsto (fun x => F (z x)) l (𝓝 w)) :
    w ∈ frontier (F '' ball (0 : ℂ) 1) := by
  have hopen : IsOpen (F '' ball (0 : ℂ) 1) :=
    RiemannInterior.isOpen_image_of_injOn isOpen_ball
      (convex_ball (0 : ℂ) 1).isPreconnected hF hinj subset_rfl isOpen_ball
  have hcl : w ∈ closure (F '' ball (0 : ℂ) 1) :=
    mem_closure_of_tendsto hw (hzin.mono fun x hx => mem_image_of_mem F hx)
  rw [hopen.frontier_eq]
  refine ⟨hcl, ?_⟩
  intro hwin
  obtain ⟨J, hJ, hJmap, hJF, _⟩ := RiemannInterior.exists_holomorphic_inverse
    isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected hF hinj
  have him : ∀ᶠ x in l, F (z x) ∈ F '' ball (0 : ℂ) 1 :=
    hzin.mono fun x hx => mem_image_of_mem F hx
  have hJlim : Tendsto (fun x => J (F (z x))) l (𝓝 (J w)) :=
    (hJ.continuousOn w hwin).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hw, him⟩)
  have hJz : Tendsto z l (𝓝 (J w)) := hJlim.congr' (hzin.mono fun x hx => hJF _ hx)
  have heq : ζ = J w := tendsto_nhds_unique hz hJz
  have hmem := hJmap hwin
  rw [mem_ball_zero_iff, ← heq, hζ] at hmem
  linarith

/-- The inward central angle of the circular cap based at `ζ`. -/
def riemannCapCenterAngle (ζ : ℂ) : ℝ := Complex.arg (-ζ)

/-- The exact half-angle cut out by the open unit disk. -/
def riemannCapHalfAngle (r : ℝ) : ℝ := Real.arccos (r / 2)

private theorem riemannCap_circle_eq {ζ : ℂ} (hζ : ‖ζ‖ = 1) (r θ : ℝ) :
    circleMap ζ r (riemannCapCenterAngle ζ + θ) = ζ * (1 - circleMap 0 r θ) := by
  have he : Complex.exp ((riemannCapCenterAngle ζ : ℂ) * Complex.I) = -ζ := by
    simpa only [riemannCapCenterAngle, norm_neg, hζ, Complex.ofReal_one, one_mul]
      using Complex.norm_mul_exp_arg_mul_I (-ζ)
  simp only [circleMap, zero_add, Complex.ofReal_add, add_mul, Complex.exp_add, he]
  ring

private theorem riemannCap_circle_norm_sq {ζ : ℂ} (hζ : ‖ζ‖ = 1) (r θ : ℝ) :
    ‖circleMap ζ r (riemannCapCenterAngle ζ + θ)‖ ^ 2 =
      1 + r ^ 2 - 2 * r * Real.cos θ := by
  rw [riemannCap_circle_eq hζ, norm_mul, hζ, one_mul,
    ← Complex.normSq_eq_norm_sq]
  calc
    Complex.normSq (1 - circleMap 0 r θ) =
        (1 - r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by
      simp [circleMap, Complex.normSq_apply, pow_two]
    _ = 1 + r ^ 2 - 2 * r * Real.cos θ := by
      linear_combination r ^ 2 * (Real.sin_sq_add_cos_sq θ)

/-- The entire open cap, including its exact angular endpoints, is
determined directly from the unit disk geometry. -/
theorem riemannCap_geometry {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
    let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
    a < b ∧ b ≤ a + 2 * Real.pi ∧
      MapsTo (circleMap ζ r) (Ioo a b) (ball (0 : ℂ) 1) ∧
      ‖circleMap ζ r a‖ = 1 ∧ ‖circleMap ζ r b‖ = 1 := by
  let α := riemannCapHalfAngle r
  have hα : 0 < α := Real.arccos_pos.2 (by linarith)
  have hαπ : α ≤ Real.pi := Real.arccos_le_pi _
  have hc : Real.cos α = r / 2 := Real.cos_arccos (by linarith) (by linarith)
  dsimp
  refine ⟨by dsimp [α] at hα; linarith,
    by dsimp [α] at hαπ; linarith, ?_, ?_, ?_⟩
  · intro θ hθ
    let u := θ - riemannCapCenterAngle ζ
    have hu : |u| < α := abs_lt.2 ⟨by dsimp [u, α]; linarith [hθ.1],
      by dsimp [u, α]; linarith [hθ.2]⟩
    have hcos : r / 2 < Real.cos u := by
      rw [← hc, ← Real.cos_abs u]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hαπ hu
    rw [mem_ball_zero_iff]
    apply (sq_lt_one_iff₀ (norm_nonneg _)).1
    have heq : θ = riemannCapCenterAngle ζ + u := by dsimp [u]; ring
    rw [heq, riemannCap_circle_norm_sq hζ]
    nlinarith
  · have heq : riemannCapCenterAngle ζ - riemannCapHalfAngle r =
        riemannCapCenterAngle ζ + -α := by dsimp [α]; ring
    have hsq : ‖circleMap ζ r (riemannCapCenterAngle ζ - riemannCapHalfAngle r)‖ ^ 2 = 1 := by
      rw [heq, riemannCap_circle_norm_sq hζ, Real.cos_neg, hc]
      ring
    nlinarith [norm_nonneg (circleMap ζ r
      (riemannCapCenterAngle ζ - riemannCapHalfAngle r))]
  · have hsq : ‖circleMap ζ r (riemannCapCenterAngle ζ + riemannCapHalfAngle r)‖ ^ 2 = 1 := by
      rw [riemannCap_circle_norm_sq hζ, hc]
      ring
    nlinarith [norm_nonneg (circleMap ζ r
      (riemannCapCenterAngle ζ + riemannCapHalfAngle r))]

/-- Genuine finite-energy boundary caps: arbitrarily small radii give
an actual cap image with finite physical frontier endpoints and image
diameter less than `ε`. This is the analytic estimate used in the
Courant–Lebesgue proof, prior to the Jordan separation step. -/
theorem riemannMapping_exists_small_boundary_cap (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r : ℝ) (G : ℝ → ℂ), 0 < r ∧ r < δ ∧ r < 1 ∧ Continuous G ∧
      let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
      let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
      EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b) ∧
      G a ∈ frontier (F '' ball (0 : ℂ) 1) ∧
      G b ∈ frontier (F '' ball (0 : ℂ) 1) ∧
      (∀ θ ∈ Icc a b, ∀ τ ∈ Icc a b, ‖G θ - G τ‖ < ε) := by
  obtain ⟨r, hr, hi, hlength⟩ := riemannMapping_exists_small_cap_length
    F hF hinj hb ζ (show 0 < min δ 1 from lt_min hδ zero_lt_one) hε
  have hrδ := hr.2.trans_le (min_le_left δ 1)
  have hr1 := hr.2.trans_le (min_le_right δ 1)
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  obtain ⟨hab, hwidth, harc, hza, hzb⟩ := riemannCap_geometry hζ hr.1 hr1
  obtain ⟨G, hGc, hGeq, hGa, hGb⟩ :=
    riemannMapping_cap_continuous_extension F hF ζ r hi hab harc
  have hfrontA : G a ∈ frontier (F '' ball (0 : ℂ) 1) := by
    letI := left_nhdsWithin_Ioo_neBot hab
    exact riemannMapping_limit_mem_frontier F hF hinj hza
      (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact harc hθ)
      (((continuous_circleMap ζ r).tendsto a).mono_left nhdsWithin_le_nhds) hGa
  have hfrontB : G b ∈ frontier (F '' ball (0 : ℂ) 1) := by
    letI := right_nhdsWithin_Ioo_neBot hab
    exact riemannMapping_limit_mem_frontier F hF hinj hzb
      (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact harc hθ)
      (((continuous_circleMap ζ r).tendsto b).mono_left nhdsWithin_le_nhds) hGb
  refine ⟨r, G, hr.1, hrδ, hr1, hGc, hGeq, hfrontA, hfrontB, ?_⟩
  intro θ hθ τ hτ
  exact (riemannMapping_cap_extension_displacement F hF ζ r hi hab hwidth harc
    hGc hGeq θ hθ τ hτ).trans_lt hlength

end PolyaNeumann

end
