module

public import Theorem12Proof.RequestProject.WindingNumber

/-!
# The jump of the winding number across a curve

For a closed Lipschitz curve `γ` that passes through `0` at `θ = 0`, whose arc
`γ([-η, η])` is injective and lies on a graph `Im w = f(Re w)`, and which stays away from `0`
on the rest of the period, the winding numbers at `is` and `-is` differ by `±1` in the limit
`s → 0⁺` (`windingNumber_jump`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- A continuous curve avoiding `z` on a compact interval stays at positive distance. -/
lemma exists_pos_le_norm_sub {γ : ℝ → ℂ} (hγ : Continuous γ) {a b : ℝ} {z : ℂ}
    (hz : ∀ θ ∈ Icc a b, γ θ ≠ z) : ∃ d > 0, ∀ θ ∈ Icc a b, d ≤ ‖γ θ - z‖ := by
  rcases (Icc a b).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, by simp [he]⟩
  obtain ⟨θ₀, hθ₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    ((hγ.sub continuous_const).norm.continuousOn)
  refine ⟨‖γ θ₀ - z‖, norm_pos_iff.mpr (sub_ne_zero.mpr (hz θ₀ hθ₀)), fun θ hθ => ?_⟩
  exact hmin hθ

/-- The integrand `γ'/(γ - z)` is interval integrable where the curve avoids `z`. -/
lemma intervalIntegrable_deriv_div {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {a b : ℝ} (hab : a ≤ b) {z : ℂ} (hz : ∀ θ ∈ Icc a b, γ θ ≠ z) :
    IntervalIntegrable (fun θ => deriv γ θ / (γ θ - z)) volume a b := by
  obtain ⟨d, hd, hdz⟩ := exists_pos_le_norm_sub hK.continuous hz
  refine IntervalIntegrable.mono_fun (intervalIntegrable_const (c := K / d)) ?_ ?_
  · exact ((measurable_deriv γ).div
      (hK.continuous.measurable.sub measurable_const)).aestronglyMeasurable
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hab] at hθ
    rw [norm_div, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK θ) hd
      (hdz θ ⟨hθ.1.le, hθ.2⟩)

/-- Along an arc avoiding `z`, `exp(-∫ₐ^θ γ'/(γ - z)) (γ(θ) - z) = γ(a) - z`. -/
lemma exp_neg_integral_mul_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {a b : ℝ} (hab : a ≤ b) {z : ℂ} (hz : ∀ θ ∈ Icc a b, γ θ ≠ z) :
    ∀ θ ∈ Icc a b,
      Complex.exp (-∫ t in a..θ, deriv γ t / (γ t - z)) * (γ θ - z) = γ a - z := by
  obtain ⟨ε, hε, hfar⟩ := exists_pos_le_norm_sub hK.continuous hz
  set f : ℝ → ℂ := (Icc a b).indicator (fun s => deriv γ s / (γ s - z)) with hf
  have hfm : Measurable f := ((measurable_deriv γ).div
    (hK.continuous.measurable.sub measurable_const)).indicator measurableSet_Icc
  have hfB : ∀ s, ‖f s‖ ≤ K / ε := by
    intro s
    by_cases hs : s ∈ Icc a b
    · rw [hf, indicator_of_mem hs, norm_div]
      exact div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK s) hε (hfar s hs)
    · rw [hf, indicator_of_notMem hs, norm_zero]; positivity
  set L : NNReal := Real.toNNReal (K / ε) with hL
  have hfB' : ∀ s, ‖f s‖ ≤ L := fun s => by
    rw [hL, Real.coe_toNNReal _ (by positivity)]; exact hfB s
  set h : ℝ → ℂ := fun t => ∫ s in a..t, f s with hh
  have hhlip : LipschitzWith L h := lipschitzWith_primitive hfm.aestronglyMeasurable hfB' a
  have hh' : h = fun t => (∫ s in (0 : ℝ)..t, f s) - ∫ s in (0 : ℝ)..a, f s := by
    have hloc : LocallyIntegrable f volume :=
      locallyIntegrable_of_bounded hfm.aestronglyMeasurable hfB
    funext t
    simp only [hh]
    rw [intervalIntegral.integral_interval_sub_left
      ((hloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable)
      ((hloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable)]
  have hderiv : ∀ᵐ x, HasDerivAt h (f x) x := by
    filter_upwards [ae_hasDerivAt_primitive_of_bounded hfm hfB] with x hx
    rw [hh']
    exact hx.sub_const _
  set φ : ℝ → ℂ := fun t => Complex.exp (-h t) * (γ t - z) with hφ
  have hφ0 : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt φ 0 x := by
    filter_upwards [hderiv, hK.ae_differentiableAt_real] with x h1 h2 hx
    rw [uIcc_of_le hab] at hx
    have hfx : f x = deriv γ x / (γ x - z) := by rw [hf, indicator_of_mem hx]
    have hne : γ x - z ≠ 0 := sub_ne_zero.mpr (hz x hx)
    have := (h1.neg.cexp).mul (h2.hasDerivAt.sub_const z)
    convert this using 1
    rw [hfx]
    field_simp
    ring
  have hR : ∀ t ∈ uIcc a b, -h t ∈ closedBall (0 : ℂ) (L * (b - a)) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    rw [mem_closedBall_zero_iff, norm_neg]
    have := hhlip.dist_le_mul t a
    have h0 : h a = 0 := by simp only [hh, intervalIntegral.integral_same]
    rw [dist_eq_norm, h0, sub_zero, Real.dist_eq, abs_of_nonneg (by linarith [ht.1])] at this
    exact this.trans (by gcongr; linarith [ht.2])
  have hexpAC : AbsolutelyContinuousOnInterval (fun t => Complex.exp (-h t)) a b :=
    ((lipschitzOnWith_cexp_closedBall _).comp hhlip.neg.lipschitzOnWith
      (fun t ht => hR t ht)).absolutelyContinuousOnInterval
  have hγAC : AbsolutelyContinuousOnInterval (fun t => γ t - z) a b :=
    (hK.sub (LipschitzWith.const z)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hAC : AbsolutelyContinuousOnInterval φ a b := hexpAC.smul hγAC
  obtain ⟨C, hC⟩ := hAC.const_of_ae_hasDerivAt_zero hφ0
  intro θ hθ
  have heq : φ θ = φ a := by
    rw [hC θ (by rw [uIcc_of_le hab]; exact hθ), hC _ left_mem_uIcc]
  have hint : ∫ t in a..θ, deriv γ t / (γ t - z) = h θ := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hθ.1] at ht
    rw [hf, indicator_of_mem (show t ∈ Icc a b from ⟨ht.1, ht.2.trans hθ.2⟩)]
  rw [hint]
  simpa only [hφ, hh, intervalIntegral.integral_same, neg_zero, Complex.exp_zero, one_mul]
    using heq

/-- Along an arc on which `c (γ - z)` stays in the slit plane, the integral of `γ'/(γ - z)` is
the increment of the branch `log (c (· - z))`. -/
lemma integral_deriv_div_eq_log_sub {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {a b : ℝ} (hab : a ≤ b) {z c : ℂ} (hc : c ≠ 0)
    (hslit : ∀ θ ∈ Icc a b, c * (γ θ - z) ∈ Complex.slitPlane) :
    ∫ t in a..b, deriv γ t / (γ t - z) =
      Complex.log (c * (γ b - z)) - Complex.log (c * (γ a - z)) := by
  have hne : ∀ θ ∈ Icc a b, γ θ - z ≠ 0 := fun θ hθ h0 => by
    have := hslit θ hθ
    rw [h0, mul_zero] at this
    exact Complex.slitPlane_ne_zero this rfl
  have hz : ∀ θ ∈ Icc a b, γ θ ≠ z := fun θ hθ => sub_ne_zero.mp (hne θ hθ)
  set H : ℝ → ℂ := fun θ => ∫ t in a..θ, deriv γ t / (γ t - z) with hH
  set ℓ : ℝ → ℂ := fun θ => Complex.log (c * (γ θ - z)) - Complex.log (c * (γ a - z))
    with hℓ
  set k : ℝ → ℂ := fun θ => (H θ - ℓ θ) / (2 * π * Complex.I) with hk
  have hHc : ContinuousOn H (Icc a b) := by
    have hii := intervalIntegrable_deriv_div hK hab hz
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hii
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (a := a) (b := b) (f := fun t => deriv γ t / (γ t - z)) (by rwa [uIcc_of_le hab])
    rwa [uIcc_of_le hab] at this
  have hℓc : ContinuousOn ℓ (Icc a b) := by
    refine ContinuousOn.sub ?_ continuousOn_const
    intro θ hθ
    exact ContinuousAt.comp_continuousWithinAt (g := Complex.log)
      (f := fun θ => c * (γ θ - z)) (continuousAt_clog (hslit θ hθ))
      ((continuous_const.mul (hK.continuous.sub continuous_const)).continuousWithinAt)
  have hkc : ContinuousOn k (Icc a b) := (hHc.sub hℓc).div_const _
  have hmaps : MapsTo k (Icc a b) (range ((↑) : ℤ → ℂ)) := by
    intro θ hθ
    have h1 := exp_neg_integral_mul_eq hK hab hz θ hθ
    have h2 : Complex.exp (ℓ θ) = (γ θ - z) / (γ a - z) := by
      simp only [hℓ]
      rw [Complex.exp_sub, Complex.exp_log (Complex.slitPlane_ne_zero (hslit θ hθ)),
        Complex.exp_log (Complex.slitPlane_ne_zero (hslit a ⟨le_rfl, hab⟩))]
      field_simp
    have h3 : Complex.exp (-(H θ - ℓ θ)) = 1 := by
      rw [neg_sub, sub_eq_add_neg, Complex.exp_add, h2]
      simp only [hH]
      rw [div_mul_eq_mul_div, mul_comm, h1, div_self (hne a ⟨le_rfl, hab⟩)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h3
    refine ⟨-n, ?_⟩
    have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    simp only [hk]
    rw [eq_div_iff h2pi, show H θ - ℓ θ = -(-(H θ - ℓ θ)) by ring, hn]
    push_cast
    ring
  have hconst := isPreconnected_Icc.constant_of_mapsTo
    (isDiscrete_iff_discreteTopology.mpr inferInstance) hkc hmaps
    (right_mem_Icc.mpr hab) (left_mem_Icc.mpr hab)
  have hka : k a = 0 := by simp [hk, hH, hℓ]
  rw [hka] at hconst
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [hk, div_eq_zero_iff, h2pi, or_false, sub_eq_zero] at hconst
  exact hconst

/-- The two branches `log (i u)` and `log (-i u)` differ by `πi` on the right half-plane. -/
lemma log_I_mul_sub_log_neg_I_mul_of_re_pos {u : ℂ} (hu : 0 < u.re) :
    Complex.log (Complex.I * u) - Complex.log (-Complex.I * u) = π * Complex.I := by
  have him : 0 < (Complex.I * u).im := by simpa using hu
  rw [neg_mul, Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos him]
  push_cast
  ring

/-- The two branches `log (i u)` and `log (-i u)` differ by `-πi` on the left half-plane. -/
lemma log_I_mul_sub_log_neg_I_mul_of_re_neg {u : ℂ} (hu : u.re < 0) :
    Complex.log (Complex.I * u) - Complex.log (-Complex.I * u) = -(π * Complex.I) := by
  have him : (Complex.I * u).im < 0 := by simpa using hu
  rw [neg_mul, Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg him]
  push_cast
  ring

/-- An injective arc on a graph through `0` has endpoints on opposite sides of the vertical
axis. -/
lemma re_mul_re_neg_of_graph {γ : ℝ → ℂ} (hγ : Continuous γ) {η : ℝ} (hη0 : 0 < η)
    {f : ℝ → ℝ} (h0 : γ 0 = 0) (hgraph : ∀ θ ∈ Icc (-η) η, (γ θ).im = f (γ θ).re)
    (hinj : InjOn γ (Icc (-η) η)) : (γ (-η)).re * (γ η).re < 0 := by
  have hxinj : InjOn (fun θ => (γ θ).re) (Icc (-η) η) := by
    intro θ₁ h₁ θ₂ h₂ he
    simp only at he
    exact hinj h₁ h₂ (Complex.ext he (by rw [hgraph θ₁ h₁, hgraph θ₂ h₂, he]))
  have hc : ContinuousOn (fun θ => (γ θ).re) (Icc (-η) η) :=
    (Complex.continuous_re.comp hγ).continuousOn
  have hm0 : (0 : ℝ) ∈ Icc (-η) η := ⟨by linarith, hη0.le⟩
  have hl : -η ∈ Icc (-η) η := ⟨le_rfl, by linarith⟩
  have hr : η ∈ Icc (-η) η := ⟨by linarith, le_rfl⟩
  rcases hc.strictMonoOn_of_injOn_Icc' (by linarith) hxinj with hm | hm
  · have h1 := hm hl hm0 (by linarith)
    have h2 := hm hm0 hr hη0
    simp only [h0, Complex.zero_re] at h1 h2
    nlinarith
  · have h1 := hm hl hm0 (by linarith)
    have h2 := hm hm0 hr hη0
    simp only [h0, Complex.zero_re] at h1 h2
    nlinarith

/-- The integral of `γ'/(γ - z)` over an arc avoiding `0` is continuous in `z` at `0`. -/
lemma continuousAt_integral_deriv_div {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {a b : ℝ} (hab : a ≤ b) (hfar : ∀ θ ∈ Icc a b, γ θ ≠ 0) :
    ContinuousAt (fun z => ∫ θ in a..b, deriv γ θ / (γ θ - z)) 0 := by
  obtain ⟨ε, hε, hd⟩ := exists_pos_le_norm_sub hK.continuous hfar
  have hfar' : ∀ z ∈ ball (0 : ℂ) (ε / 2), ∀ θ ∈ Icc a b, ε / 2 ≤ ‖γ θ - z‖ := by
    intro z hz θ hθ
    have h1 := hd θ hθ
    rw [sub_zero] at h1
    have h2 : ‖z‖ < ε / 2 := mem_ball_zero_iff.mp hz
    have := norm_sub_norm_le (γ θ) z
    linarith
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => K / (ε / 2))
    ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun z => ((measurable_deriv γ).div
      (hK.continuous.measurable.sub measurable_const)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds (0 : ℂ) (half_pos hε)] with z hz
    refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hab] at hθ
    rw [norm_div]
    exact div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK θ) (half_pos hε)
      (hfar' z hz θ ⟨hθ.1.le, hθ.2⟩)
  · refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hab] at hθ
    have hne : γ θ - 0 ≠ 0 := by rw [sub_zero]; exact hfar θ ⟨hθ.1.le, hθ.2⟩
    exact continuousAt_const.div (continuousAt_const.sub continuousAt_id) hne

/-- For a `2π`-periodic Lipschitz curve avoiding `z` on `[a, a + 2π]`, the winding number
splits at any intermediate point. -/
lemma windingNumber_eq_split {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ (2 * π)) {a m : ℝ} (ham : a ≤ m) (hm : m ≤ a + 2 * π) {z : ℂ}
    (hz : ∀ θ ∈ Icc a (a + 2 * π), γ θ ≠ z) :
    windingNumber γ z = (2 * π * Complex.I)⁻¹ *
      ((∫ θ in a..m, deriv γ θ / (γ θ - z)) + ∫ θ in m..(a + 2 * π), deriv γ θ / (γ θ - z)) := by
  have hdper : Function.Periodic (deriv γ) (2 * π) := by
    intro θ
    have h1 : (fun x => γ (x + 2 * π)) = γ := funext hper
    rw [← deriv_comp_add_const, h1]
  have hgp : Function.Periodic (fun θ => deriv γ θ / (γ θ - z)) (2 * π) := by
    intro θ; simp only [hdper θ, hper θ]
  rw [windingNumber]
  congr 1
  have := hgp.intervalIntegral_add_eq 0 a
  rw [zero_add] at this
  rw [this, intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_deriv_div hK ham fun θ hθ => hz θ ⟨hθ.1, hθ.2.trans hm⟩)
    (intervalIntegrable_deriv_div hK hm fun θ hθ => hz θ ⟨ham.trans hθ.1, hθ.2⟩)]

/-- Continuity of a logarithm branch along a vertical approach. -/
lemma tendsto_log_mul_sub {c w e : ℂ} (h : c * w ∈ Complex.slitPlane) :
    Tendsto (fun s : ℝ => Complex.log (c * (w - s * e))) (𝓝[>] 0)
      (𝓝 (Complex.log (c * w))) := by
  have hc : Continuous (fun s : ℝ => c * (w - (s : ℂ) * e)) := by fun_prop
  have := (continuousAt_clog h).tendsto.comp (hc.tendsto' 0 (c * w) (by simp))
  exact tendsto_nhdsWithin_of_tendsto_nhds this

/-- **Jump of the winding number.** Let `γ` be a `2π`-periodic Lipschitz curve with
`γ(0) = 0`, injective on `[-η, η]` (`0 < η < π`), with `γ([-η, η])` contained in a graph
`Im w = f(Re w)`, and `γ(θ) ≠ 0` for `θ ∈ [η, 2π - η]`. Then
`wind(γ, is) - wind(γ, -is) → σ` as `s → 0⁺` for some `σ = ±1`. -/
theorem windingNumber_jump {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ (2 * π)) {η : ℝ} (hη0 : 0 < η) (hηπ : η < π)
    {f : ℝ → ℝ} (h0 : γ 0 = 0) (hgraph : ∀ θ ∈ Icc (-η) η, (γ θ).im = f (γ θ).re)
    (hinj : InjOn γ (Icc (-η) η)) (hfar : ∀ θ ∈ Icc η (2 * π - η), γ θ ≠ 0) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      Tendsto (fun s : ℝ => windingNumber γ (s * Complex.I) -
        windingNumber γ (-(s * Complex.I))) (𝓝[>] 0) (𝓝 σ) := by
  have hηη : -η ≤ η := by linarith
  have hm2 : η ≤ -η + 2 * π := by linarith
  have hfar' : ∀ θ ∈ Icc η (-η + 2 * π), γ θ ≠ 0 := fun θ hθ =>
    hfar θ ⟨hθ.1, by linarith [hθ.2]⟩
  obtain ⟨d, hd, hdfar⟩ := exists_pos_le_norm_sub hK.continuous hfar'
  have hf0 : f 0 = 0 := by
    have := hgraph 0 ⟨by linarith, hη0.le⟩
    rw [h0] at this
    simpa using this.symm
  set α := γ (-η) with hα
  set β := γ η with hβ
  have hαβ : α.re * β.re < 0 := re_mul_re_neg_of_graph hK.continuous hη0 h0 hgraph hinj
  have hαne : α.re ≠ 0 := fun h => by rw [h, zero_mul] at hαβ; exact lt_irrefl _ hαβ
  have hβne : β.re ≠ 0 := fun h => by rw [h, mul_zero] at hαβ; exact lt_irrefl _ hαβ
  set N : ℂ → ℂ := fun z => ∫ θ in (-η)..η, deriv γ θ / (γ θ - z) with hN
  set F : ℂ → ℂ := fun z => ∫ θ in η..(-η + 2 * π), deriv γ θ / (γ θ - z) with hF
  have hslitP : ∀ s : ℝ, 0 < s → ∀ θ ∈ Icc (-η) η,
      Complex.I * (γ θ - s * Complex.I) ∈ Complex.slitPlane := by
    intro s hs θ hθ
    rw [Complex.mem_slitPlane_iff]
    by_cases hx : (γ θ).re = 0
    · left
      have hy : (γ θ).im = 0 := by rw [hgraph θ hθ, hx, hf0]
      simp [hy, hs]
    · right; simpa using hx
  have hslitN : ∀ s : ℝ, 0 < s → ∀ θ ∈ Icc (-η) η,
      -Complex.I * (γ θ - -(s * Complex.I)) ∈ Complex.slitPlane := by
    intro s hs θ hθ
    rw [Complex.mem_slitPlane_iff]
    by_cases hx : (γ θ).re = 0
    · left
      have hy : (γ θ).im = 0 := by rw [hgraph θ hθ, hx, hf0]
      simp [hy, hs]
    · right; simpa using hx
  have hnearP : ∀ s : ℝ, 0 < s → N (s * Complex.I) =
      Complex.log (Complex.I * (β - s * Complex.I)) -
        Complex.log (Complex.I * (α - s * Complex.I)) := fun s hs =>
    integral_deriv_div_eq_log_sub hK hηη Complex.I_ne_zero (hslitP s hs)
  have hnearN : ∀ s : ℝ, 0 < s → N (-(s * Complex.I)) =
      Complex.log (-Complex.I * (β - -(s * Complex.I))) -
        Complex.log (-Complex.I * (α - -(s * Complex.I))) := fun s hs =>
    integral_deriv_div_eq_log_sub hK hηη (neg_ne_zero.mpr Complex.I_ne_zero) (hslitN s hs)
  have hav : ∀ s : ℝ, 0 < s → s < d → ∀ z : ℂ, ‖z‖ = s →
      (∀ θ ∈ Icc (-η) η, γ θ ≠ z) → ∀ θ ∈ Icc (-η) (-η + 2 * π), γ θ ≠ z := by
    intro s hs hsd z hz hnear θ hθ
    by_cases hθη : θ ≤ η
    · exact hnear θ ⟨hθ.1, hθη⟩
    · intro heq
      have := hdfar θ ⟨(not_le.mp hθη).le, hθ.2⟩
      rw [heq, sub_zero, hz] at this
      linarith
  have hneP : ∀ s : ℝ, 0 < s → ∀ θ ∈ Icc (-η) η, γ θ ≠ s * Complex.I := by
    intro s hs θ hθ h
    have := hslitP s hs θ hθ
    rw [h, sub_self, mul_zero] at this
    exact Complex.slitPlane_ne_zero this rfl
  have hneN : ∀ s : ℝ, 0 < s → ∀ θ ∈ Icc (-η) η, γ θ ≠ -(s * Complex.I) := by
    intro s hs θ hθ h
    have := hslitN s hs θ hθ
    rw [h, sub_self, mul_zero] at this
    exact Complex.slitPlane_ne_zero this rfl
  have hnormP : ∀ s : ℝ, 0 < s → ‖(s : ℂ) * Complex.I‖ = s := fun s hs => by
    simp [abs_of_pos hs]
  have hnormN : ∀ s : ℝ, 0 < s → ‖-((s : ℂ) * Complex.I)‖ = s := fun s hs => by
    simp [abs_of_pos hs]
  have heq : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), windingNumber γ ((s : ℂ) * Complex.I) -
      windingNumber γ (-((s : ℂ) * Complex.I)) = (2 * π * Complex.I)⁻¹ *
        ((N ((s : ℂ) * Complex.I) - N (-((s : ℂ) * Complex.I))) +
          (F ((s : ℂ) * Complex.I) - F (-((s : ℂ) * Complex.I)))) := by
    filter_upwards [Ioo_mem_nhdsGT hd] with s hs
    rw [windingNumber_eq_split hK hper hηη hm2
        (hav s hs.1 hs.2 _ (hnormP s hs.1) (hneP s hs.1)),
      windingNumber_eq_split hK hper hηη hm2
        (hav s hs.1 hs.2 _ (hnormN s hs.1) (hneN s hs.1))]
    ring
  have hβP : Complex.I * β ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simpa using hβne
  have hαP : Complex.I * α ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simpa using hαne
  have hβN : -Complex.I * β ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simpa using hβne
  have hαN : -Complex.I * α ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simpa using hαne
  have hNlim : Tendsto (fun s : ℝ => N (s * Complex.I) - N (-(s * Complex.I))) (𝓝[>] 0)
      (𝓝 ((Complex.log (Complex.I * β) - Complex.log (Complex.I * α)) -
        (Complex.log (-Complex.I * β) - Complex.log (-Complex.I * α)))) := by
    have e : (fun s : ℝ => (Complex.log (Complex.I * (β - s * Complex.I)) -
          Complex.log (Complex.I * (α - s * Complex.I))) -
        (Complex.log (-Complex.I * (β - s * -Complex.I)) -
          Complex.log (-Complex.I * (α - s * -Complex.I)))) =ᶠ[𝓝[>] 0]
        fun s : ℝ => N (s * Complex.I) - N (-(s * Complex.I)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [hnearP s hs, hnearN s hs, mul_neg]
    exact Tendsto.congr' e (((tendsto_log_mul_sub hβP).sub (tendsto_log_mul_sub hαP)).sub
      ((tendsto_log_mul_sub hβN).sub (tendsto_log_mul_sub hαN)))
  have hFc : ContinuousAt F 0 := continuousAt_integral_deriv_div hK hm2 hfar'
  have hFlim : Tendsto (fun s : ℝ => F (s * Complex.I) - F (-(s * Complex.I))) (𝓝[>] 0)
      (𝓝 (F 0 - F 0)) := by
    have h1 : Tendsto (fun s : ℝ => (s : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds
        ((Complex.continuous_ofReal.mul continuous_const).tendsto' 0 0 (by simp))
    have h2 : Tendsto (fun s : ℝ => -((s : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 0) := by
      simpa using h1.neg
    exact (hFc.tendsto.comp h1).sub (hFc.tendsto.comp h2)
  have hlim := (tendsto_const_nhds (x := (2 * π * Complex.I)⁻¹)).mul (hNlim.add hFlim)
  have hlim' := hlim.congr' (EventuallyEq.symm heq)
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rcases lt_or_gt_of_ne hαne with hαneg | hαpos
  · have hβpos : 0 < β.re := by nlinarith
    refine ⟨1, Or.inl rfl, ?_⟩
    convert hlim' using 2
    rw [sub_self, add_zero, show ∀ a b c e : ℂ, (a - b) - (c - e) = (a - c) - (b - e) by
      intros; ring, log_I_mul_sub_log_neg_I_mul_of_re_pos hβpos,
      log_I_mul_sub_log_neg_I_mul_of_re_neg hαneg]
    field_simp
    ring
  · have hβneg : β.re < 0 := by nlinarith
    refine ⟨-1, Or.inr rfl, ?_⟩
    convert hlim' using 2
    rw [sub_self, add_zero, show ∀ a b c e : ℂ, (a - b) - (c - e) = (a - c) - (b - e) by
      intros; ring, log_I_mul_sub_log_neg_I_mul_of_re_neg hβneg,
      log_I_mul_sub_log_neg_I_mul_of_re_pos hαpos]
    field_simp
    ring

end PolyaNeumann

end
