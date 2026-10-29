/-
Extracted from RequestProject/RiemannMappingCaratheodory.lean in the prior
Apache-2.0 Neumann development at commit b37a190b8afc6efb128f204176d26deec8d88a8c.
The source project records its authors and assistance; its license is kept
in licenses/NEUMANN_SOURCE_LICENSE.txt. Only the boundary uniqueness and circle-patch
lemmas are included here.
-/
module

public import Theorem12Proof.RequestProject.RiemannMappingCapWinding
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open Set Metric Filter MeasureTheory Complex
open scoped Topology ComplexConjugate
private theorem circleDensityCauchy_differentiableOn_of_zero_near
    (g : ℝ → ℂ) (hg : Continuous g) {ζ : ℂ} {d : ℝ} (hd : 0 < d)
    (hzero : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖circleMap 0 1 θ - ζ‖ < d → g θ = 0) :
    DifferentiableOn ℂ (fun w : ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (circleMap 0 1 θ - w))
      (ball ζ (d / 2)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * Real.pi)) hg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hsep (θ : ℝ) (_hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi))
      (hfar : d ≤ ‖circleMap 0 1 θ - ζ‖) (w : ℂ) (hw : w ∈ ball ζ (d / 2)) :
      d / 2 ≤ ‖circleMap 0 1 θ - w‖ := by
    have hw' : ‖w - ζ‖ < d / 2 := by simpa only [mem_ball, dist_eq_norm] using hw
    have htri : ‖circleMap 0 1 θ - ζ‖ ≤ ‖circleMap 0 1 θ - w‖ + ‖w - ζ‖ := by
      calc
        _ = ‖(circleMap 0 1 θ - w) + (w - ζ)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    linarith
  have hquot (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi))
      (w : ℂ) (hw : w ∈ ball ζ (d / 2)) :
      ‖g θ / (circleMap 0 1 θ - w)‖ ≤ M / (d / 2) := by
    by_cases hn : ‖circleMap 0 1 θ - ζ‖ < d
    · rw [hzero θ hθ hn, zero_div, norm_zero]
      exact div_nonneg hM0 (half_pos hd).le
    · rw [norm_div]
      exact div_le_div₀ hM0 (hM θ hθ) (half_pos hd)
        (hsep θ hθ (le_of_not_gt hn) w hw)
  have hderivBound (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) (2 * Real.pi))
      (w : ℂ) (hw : w ∈ ball ζ (d / 2)) :
      ‖g θ / (circleMap 0 1 θ - w) ^ 2‖ ≤ M / (d / 2) ^ 2 := by
    by_cases hn : ‖circleMap 0 1 θ - ζ‖ < d
    · rw [hzero θ hθ hn, zero_div, norm_zero]
      exact div_nonneg hM0 (sq_nonneg _)
    · rw [norm_div, norm_pow]
      exact div_le_div₀ hM0 (hM θ hθ) (sq_pos_of_pos (half_pos hd))
        ((sq_le_sq₀ (half_pos hd).le (norm_nonneg _)).mpr
          (hsep θ hθ (le_of_not_gt hn) w hw))
  intro w₀ hw₀
  have hmeas (w : ℂ) : AEStronglyMeasurable
      (fun θ : ℝ => g θ / (circleMap 0 1 θ - w))
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (hg.measurable.div ((measurable_circleMap 0 1).sub measurable_const)).aestronglyMeasurable
  have hFi : Integrable (fun θ : ℝ => g θ / (circleMap 0 1 θ - w₀))
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    apply (integrable_const (M / (d / 2))).mono' (hmeas w₀)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact hquot θ ⟨hθ.1.le, hθ.2⟩ w₀ hw₀
  have hb : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      ∀ w ∈ ball ζ (d / 2),
        ‖g θ / (circleMap 0 1 θ - w) ^ 2‖ ≤ M / (d / 2) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact hderivBound θ ⟨hθ.1.le, hθ.2⟩
  have hdif : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      ∀ w ∈ ball ζ (d / 2),
        HasDerivAt (fun v : ℂ => g θ / (circleMap 0 1 θ - v))
          (g θ / (circleMap 0 1 θ - w) ^ 2) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    intro w hw
    have hθ' : θ ∈ Icc (0 : ℝ) (2 * Real.pi) := ⟨hθ.1.le, hθ.2⟩
    by_cases hn : ‖circleMap 0 1 θ - ζ‖ < d
    · simp only [hzero θ hθ' hn, zero_div]
      exact hasDerivAt_const w 0
    · have hne : circleMap 0 1 θ - w ≠ 0 := norm_pos_iff.mp
        (lt_of_lt_of_le (half_pos hd) (hsep θ hθ' (le_of_not_gt hn) w hw))
      simpa only [Pi.div_apply, zero_mul, mul_neg, mul_one, zero_sub, neg_neg] using!
        (hasDerivAt_const w (g θ)).div
          ((hasDerivAt_const w (circleMap 0 1 θ)).sub (hasDerivAt_id w)) hne
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))
    (F := fun w θ => g θ / (circleMap 0 1 θ - w))
    (F' := fun w θ => g θ / (circleMap 0 1 θ - w) ^ 2)
    (bound := fun _ : ℝ => M / (d / 2) ^ 2)
    (isOpen_ball.mem_nhds hw₀) (Eventually.of_forall hmeas) hFi
    (hg.measurable.div
      (((measurable_circleMap 0 1).sub measurable_const).pow_const 2)).aestronglyMeasurable
    hb (integrable_const _) hdif
  have ht : HasDerivAt (fun w : ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (circleMap 0 1 θ - w))
      (∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (circleMap 0 1 θ - w₀) ^ 2) w₀ := by
    simpa only [intervalIntegral.integral_of_le Real.two_pi_pos.le] using hdiff.2
  exact ht.differentiableAt.differentiableWithinAt

/-- Boundary uniqueness on a genuine open circle patch. The proof
continues the actual Cauchy integral across the patch where its density
vanishes, then uses its exterior zero values and the analytic identity
principle. No reflection theorem or boundary differentiability is a
premise. -/
theorem diffContOnCl_eq_zero_of_circle_patch
    (G : ℂ → ℂ) (hG : DiffContOnCl ℂ G (ball (0 : ℂ) 1))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {d : ℝ} (hd : 0 < d)
    (hzero : ∀ z ∈ sphere (0 : ℂ) 1, ‖z - ζ‖ < d → G z = 0) :
    EqOn G 0 (ball (0 : ℂ) 1) := by
  let C : ℂ → ℂ := fun w => circleIntegral (fun z => (z - w)⁻¹ * G z) 0 1
  let g : ℝ → ℂ := fun θ => deriv (circleMap 0 1) θ * G (circleMap 0 1 θ)
  have hγc : Continuous (circleMap (0 : ℂ) 1) := continuous_circleMap 0 1
  have hgc : Continuous g :=
    ((contDiff_circleMap 0 1 : ContDiff ℝ 1 (circleMap (0 : ℂ) 1)).continuous_deriv_one).mul
      (hG.continuousOn_ball.comp_continuous hγc fun θ =>
        sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ))
  have hCint : C = fun w : ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (circleMap 0 1 θ - w) := by
    funext w
    dsimp [C, g, circleIntegral]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [div_eq_mul_inv]
    ring
  have hCd : DifferentiableOn ℂ C (ball ζ (d / 2)) := by
    rw [hCint]
    apply circleDensityCauchy_differentiableOn_of_zero_near g hgc hd
    intro θ _hθ hn
    dsimp [g]
    rw [hzero _ (circleMap_mem_sphere 0 zero_le_one θ) hn, mul_zero]
  have hCinside (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) :
      C w = (2 * Real.pi * I : ℂ) * G w := by
    simpa only [C, smul_eq_mul] using hG.circleIntegral_sub_inv_smul hw
  have hCoutside (w : ℂ) (hw : 1 < ‖w‖) : C w = 0 := by
    have hne : ∀ z ∈ closure (ball (0 : ℂ) 1), z - w ≠ 0 := by
      intro z hz hzw
      have hzn : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp (closure_ball_subset_closedBall hz)
      have he : z = w := sub_eq_zero.mp hzw
      exact (not_le_of_gt hw) (he ▸ hzn)
    have hsub : DiffContOnCl ℂ (fun z : ℂ => z - w) (ball (0 : ℂ) 1) :=
      ((differentiable_id : Differentiable ℂ (fun z : ℂ => z)).sub_const w).diffContOnCl
    have hquot := (hsub.inv hne).smul hG
    simpa only [C, Pi.inv_apply, smul_eq_mul] using hquot.circleIntegral_eq_zero zero_le_one
  let e := min (d / 4) (1 / 2 : ℝ)
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have hehalf : e < d / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have heone : e < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let wout : ℂ := (1 + e) • ζ
  have hwoutn : ‖wout‖ = 1 + e := by
    simp only [wout, norm_smul, Real.norm_eq_abs, hζ, mul_one, abs_of_pos (by linarith : 0 < 1 + e)]
  have hwout : wout ∈ ball ζ (d / 2) := by
    rw [mem_ball, dist_eq_norm]
    have heq : wout - ζ = e • ζ := by
      change (1 + e) • ζ - ζ = e • ζ
      rw [add_smul, one_smul]
      abel
    rw [heq, norm_smul, hζ, mul_one, Real.norm_eq_abs, abs_of_pos he]
    exact hehalf
  have hCevent : C =ᶠ[𝓝 wout] 0 := by
    have ho : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [ho.mem_nhds (by change 1 < ‖wout‖; rw [hwoutn]; linarith)] with w hw
    exact hCoutside w hw
  have hCzero : EqOn C 0 (ball ζ (d / 2)) :=
    hCd.analyticOnNhd isOpen_ball |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball ζ (d / 2)).isPreconnected hwout hCevent
  let win : ℂ := (1 - e) • ζ
  have hwinn : ‖win‖ = 1 - e := by
    simp only [win, norm_smul, Real.norm_eq_abs, hζ, mul_one, abs_of_pos (sub_pos.mpr heone)]
  have hwinD : win ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hwinn]
    linarith
  have hwinB : win ∈ ball ζ (d / 2) := by
    rw [mem_ball, dist_eq_norm]
    have heq : win - ζ = (-e) • ζ := by
      change (1 - e) • ζ - ζ = (-e) • ζ
      rw [sub_smul, one_smul, neg_smul]
      abel
    rw [heq, norm_smul, hζ, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos he]
    exact hehalf
  have hcne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hGevent : G =ᶠ[𝓝 win] 0 := by
    filter_upwards [isOpen_ball.mem_nhds hwinD, isOpen_ball.mem_nhds hwinB] with w hwD hwB
    have hz : (2 * Real.pi * I : ℂ) * G w = 0 := (hCinside w hwD).symm.trans (hCzero hwB)
    exact (mul_eq_zero.mp hz).resolve_left hcne
  exact hG.differentiableOn.analyticOnNhd isOpen_ball
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      hwinD hGevent

private theorem unitCircle_mem_slitPlane_of_ne_neg_one {z : ℂ}
    (hz : ‖z‖ = 1) (hne : z ≠ -1) : z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : z.im = 0
  · left
    have hsq : z.re * z.re = 1 := by
      have ht := normSq_eq_norm_sq z
      rw [normSq_apply, hz, him] at ht
      nlinarith
    have hrne : z.re ≠ -1 := by
      intro hr
      apply hne
      apply Complex.ext
      · simpa only [neg_re, one_re] using hr
      · simpa only [neg_im, one_im, neg_zero] using him
    have hor : z.re = 1 ∨ z.re = -1 :=
      mul_self_eq_mul_self_iff.mp (by simpa only [one_mul] using hsq)
    rw [hor.resolve_right hrne]
    exact zero_lt_one
  · exact Or.inr him

/-- Any nontrivial connected proper subset of the actual unit circle
contains a relatively open circle patch. The argument cut is chosen at
an actual circle point outside the set; no circle-arc premise is used. -/
theorem exists_circle_patch_subset_of_preconnected
    {A : Set ℂ} (hA : IsPreconnected A) (hAs : A ⊆ sphere (0 : ℂ) 1)
    {η : ℂ} (hη : ‖η‖ = 1) (hηA : η ∉ A)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ A) (hz₂ : z₂ ∈ A) (h12 : z₁ ≠ z₂) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ z ∈ sphere (0 : ℂ) 1, ‖z - ζ‖ < d → z ∈ A := by
  let u : ℂ → ℂ := fun z => -conj η * z
  have hucont : Continuous u := continuous_const.mul continuous_id
  have hηconj : η * conj η = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, hη]
    norm_num
  have huinv (z : ℂ) : (-η) * u z = z := by
    dsimp [u]
    calc
      (-η) * (-conj η * z) = (η * conj η) * z := by ring
      _ = z := by rw [hηconj, one_mul]
  have hunorm {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : ‖u z‖ = 1 := by
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    simp only [u, norm_mul, norm_neg, norm_conj, hη, hzn, one_mul]
  have huslit (z : ℂ) (hz : z ∈ A) : u z ∈ slitPlane := by
    apply unitCircle_mem_slitPlane_of_ne_neg_one (hunorm (hAs hz))
    intro he
    have hze : z = η := by
      calc
        z = (-η) * u z := (huinv z).symm
        _ = η := by rw [he]; ring
    exact hηA (hze ▸ hz)
  let f : ℂ → ℝ := fun z => arg (u z)
  have hfcont : ContinuousOn f A := by
    intro z hz
    exact ((continuousAt_arg (huslit z hz)).comp hucont.continuousAt).continuousWithinAt
  have hfconn : IsPreconnected (f '' A) := hA.image f hfcont
  have hf_inj {z w : ℂ} (hz : z ∈ sphere (0 : ℂ) 1)
      (hw : w ∈ sphere (0 : ℂ) 1) (he : f z = f w) : z = w := by
    have hue : u z = u w := ext_norm_arg_iff.mpr
      ⟨(hunorm hz).trans (hunorm hw).symm, he⟩
    exact (huinv z).symm.trans ((congrArg (fun v : ℂ => (-η) * v) hue).trans (huinv w))
  have hargne : f z₁ ≠ f z₂ := fun he => h12 (hf_inj (hAs hz₁) (hAs hz₂) he)
  have hbuild (a b : ℝ) (hab : a < b) (ha : a ∈ f '' A) (hb : b ∈ f '' A) :
      ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ d : ℝ, 0 < d ∧
        ∀ z ∈ sphere (0 : ℂ) 1, ‖z - ζ‖ < d → z ∈ A := by
    have hm : (a + b) / 2 ∈ f '' A := hfconn.Icc_subset ha hb ⟨by linarith, by linarith⟩
    obtain ⟨ζ, hζA, hζm⟩ := hm
    have hζs : ζ ∈ sphere (0 : ℂ) 1 := hAs hζA
    have hfζ : ContinuousAt f ζ := (continuousAt_arg (huslit ζ hζA)).comp hucont.continuousAt
    have hmI : f ζ ∈ Ioo a b := by rw [hζm]; constructor <;> linarith
    obtain ⟨d, hd, hdb⟩ := Metric.mem_nhds_iff.mp (hfζ (isOpen_Ioo.mem_nhds hmI))
    refine ⟨ζ, by simpa only [mem_sphere, dist_zero_right] using hζs, d, hd, ?_⟩
    intro z hzs hzn
    have hfz : f z ∈ Ioo a b := hdb (by simpa only [mem_ball, dist_eq_norm] using hzn)
    have hfzim : f z ∈ f '' A := hfconn.Icc_subset ha hb ⟨hfz.1.le, hfz.2.le⟩
    obtain ⟨w, hwA, hwe⟩ := hfzim
    have hzw : z = w := hf_inj hzs (hAs hwA) hwe.symm
    exact hzw.symm ▸ hwA
  rcases lt_or_gt_of_ne hargne with hlt | hgt
  · exact hbuild (f z₁) (f z₂) hlt (mem_image_of_mem f hz₁) (mem_image_of_mem f hz₂)
  · exact hbuild (f z₂) (f z₁) hgt (mem_image_of_mem f hz₂) (mem_image_of_mem f hz₁)


end PolyaNeumann

