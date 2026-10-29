module

public import Theorem12Proof.RequestProject.GreenWinding

/-!
# Winding numbers of closed Lipschitz curves

For a closed Lipschitz curve `γ` (`γ(2π) = γ(0)`) and `z ∉ γ([0, 2π])`:

* `PolyaNeumann.windingNumber_mem_range_intCast`: the winding number is an integer;
* `PolyaNeumann.continuousOn_windingNumber`: it is continuous off the curve;
* `PolyaNeumann.windingNumber_eq_zero_of_far`: it vanishes far from the curve;
* `PolyaNeumann.windingNumber_const_of_isPreconnected`: it is constant on preconnected sets
  avoiding the curve.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- Lebesgue differentiation for the primitive of a bounded measurable complex function. -/
lemma ae_hasDerivAt_primitive_of_bounded {f : ℝ → ℂ} {M : ℝ} (hfm : Measurable f)
    (hB : ∀ x, ‖f x‖ ≤ M) : ∀ᵐ x, HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, f t) (f x) x := by
  have hf : LocallyIntegrable f volume := locallyIntegrable_of_bounded hfm.aestronglyMeasurable hB
  have hre : LocallyIntegrable (fun t => (f t).re) volume :=
    locallyIntegrable_of_bounded (Complex.measurable_re.comp hfm).aestronglyMeasurable
      (fun x => (Complex.abs_re_le_norm _).trans (hB x))
  have him : LocallyIntegrable (fun t => (f t).im) volume :=
    locallyIntegrable_of_bounded (Complex.measurable_im.comp hfm).aestronglyMeasurable
      (fun x => (Complex.abs_im_le_norm _).trans (hB x))
  have hii : ∀ x : ℝ, IntervalIntegrable f volume 0 x := fun x =>
    (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have heq : (fun x => ∫ t in (0 : ℝ)..x, f t) = fun x =>
      ((∫ t in (0 : ℝ)..x, (f t).re : ℝ) : ℂ) +
        ((∫ t in (0 : ℝ)..x, (f t).im : ℝ) : ℂ) * Complex.I := by
    funext x
    rw [← Complex.re_add_im (∫ t in (0 : ℝ)..x, f t)]
    congr 2
    · rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm (hii x)]; rfl
    · rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm (hii x)]; rfl
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hre,
    LocallyIntegrable.ae_hasDerivAt_integral him] with x h1 h2
  rw [heq]
  have := ((h1 0).ofReal_comp).add (((h2 0).ofReal_comp).mul_const Complex.I)
  convert this using 1
  exact (Complex.re_add_im (f x)).symm

/-- The complex exponential is Lipschitz on closed balls about `0`. -/
lemma lipschitzOnWith_cexp_closedBall (R : ℝ) :
    LipschitzOnWith (Real.toNNReal (Real.exp R)) Complex.exp (closedBall 0 R) := by
  refine (convex_closedBall (0 : ℂ) R).lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => Complex.differentiableAt_exp) (fun x hx => ?_)
  rw [Complex.deriv_exp, ← NNReal.coe_le_coe, coe_nnnorm,
    Real.coe_toNNReal _ (Real.exp_pos R).le, Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm x).trans (by simpa using hx))

/-- The winding number of a closed Lipschitz curve about a point off the curve is an
integer. -/
theorem windingNumber_mem_range_intCast {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {z : ℂ} (hz : z ∉ γ '' Icc 0 (2 * π)) :
    windingNumber γ z ∈ range ((↑) : ℤ → ℂ) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hclosedImg : IsClosed (γ '' Icc 0 (2 * π)) :=
    (isCompact_Icc.image hK.continuous).isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosedImg.isOpen_compl z hz
  have hfar : ∀ θ ∈ Icc 0 (2 * π), ε ≤ ‖γ θ - z‖ := by
    intro θ hθ
    by_contra h
    push_neg at h
    exact hball (mem_ball_iff_norm.mpr h) (mem_image_of_mem γ hθ)
  set f : ℝ → ℂ := (Icc 0 (2 * π)).indicator (fun s => deriv γ s / (γ s - z)) with hf
  have hfm : Measurable f := ((measurable_deriv γ).div
    (hK.continuous.measurable.sub measurable_const)).indicator measurableSet_Icc
  have hfB : ∀ s, ‖f s‖ ≤ K / ε := by
    intro s
    by_cases hs : s ∈ Icc 0 (2 * π)
    · rw [hf, indicator_of_mem hs, norm_div]
      exact div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK s) hε (hfar s hs)
    · rw [hf, indicator_of_notMem hs, norm_zero]; positivity
  set L : NNReal := Real.toNNReal (K / ε) with hL
  have hfB' : ∀ s, ‖f s‖ ≤ L := fun s => by
    rw [hL, Real.coe_toNNReal _ (by positivity)]; exact hfB s
  set h : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, f s with hh
  have hhlip : LipschitzWith L h := lipschitzWith_primitive hfm.aestronglyMeasurable hfB' 0
  have hderiv : ∀ᵐ x, HasDerivAt h (f x) x := ae_hasDerivAt_primitive_of_bounded hfm hfB
  set φ : ℝ → ℂ := fun t => Complex.exp (-h t) * (γ t - z) with hφ
  have hφ0 : ∀ᵐ x, x ∈ uIcc 0 (2 * π) → HasDerivAt φ 0 x := by
    filter_upwards [hderiv, hK.ae_differentiableAt_real] with x h1 h2 hx
    rw [uIcc_of_le hpi.le] at hx
    have hfx : f x = deriv γ x / (γ x - z) := by rw [hf, indicator_of_mem hx]
    have hne : γ x - z ≠ 0 := by
      intro h0
      have := hfar x hx
      rw [h0, norm_zero] at this
      linarith
    have := (h1.neg.cexp).mul (h2.hasDerivAt.sub_const z)
    convert this using 1
    rw [hfx]
    field_simp
    ring
  have hR : ∀ t ∈ uIcc 0 (2 * π), -h t ∈ closedBall (0 : ℂ) (L * (2 * π)) := by
    intro t ht
    rw [uIcc_of_le hpi.le] at ht
    rw [mem_closedBall_zero_iff, norm_neg]
    have := hhlip.dist_le_mul t 0
    have h0 : h 0 = 0 := by simp only [hh, intervalIntegral.integral_same]
    rw [dist_eq_norm, h0, sub_zero, Real.dist_eq, sub_zero, abs_of_nonneg ht.1] at this
    exact this.trans (by gcongr; exact ht.2)
  have hexpAC : AbsolutelyContinuousOnInterval (fun t => Complex.exp (-h t)) 0 (2 * π) :=
    ((lipschitzOnWith_cexp_closedBall _).comp hhlip.neg.lipschitzOnWith
      (fun t ht => hR t ht)).absolutelyContinuousOnInterval
  have hγAC : AbsolutelyContinuousOnInterval (fun t => γ t - z) 0 (2 * π) :=
    (hK.sub (LipschitzWith.const z)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hAC : AbsolutelyContinuousOnInterval φ 0 (2 * π) := hexpAC.smul hγAC
  obtain ⟨C, hC⟩ := hAC.const_of_ae_hasDerivAt_zero hφ0
  have heq : φ (2 * π) = φ 0 := by rw [hC _ right_mem_uIcc, hC _ left_mem_uIcc]
  simp only [hφ, hh, intervalIntegral.integral_same, neg_zero, Complex.exp_zero, one_mul,
    hclosed] at heq
  have hne0 : γ 0 - z ≠ 0 := by
    intro h0
    have := hfar 0 ⟨le_rfl, hpi.le⟩
    rw [h0, norm_zero] at this
    linarith
  have hexp1 : Complex.exp (-∫ s in (0 : ℝ)..(2 * π), f s) = 1 :=
    mul_right_cancel₀ hne0 (heq.trans (one_mul _).symm)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
  have hint : ∫ θ in (0 : ℝ)..(2 * π), deriv γ θ / (γ θ - z) =
      ∫ s in (0 : ℝ)..(2 * π), f s := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le hpi.le] at hθ
    rw [hf, indicator_of_mem hθ]
  refine ⟨-n, ?_⟩
  rw [windingNumber, hint, show (∫ s in (0 : ℝ)..(2 * π), f s) = -(n * (2 * π * Complex.I)) by
    rw [← hn, neg_neg]]
  have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  push_cast
  field_simp

/-- The winding number is continuous off the curve. -/
theorem continuousOn_windingNumber {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) :
    ContinuousOn (windingNumber γ) (γ '' Icc 0 (2 * π))ᶜ := by
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  have hclosedImg : IsClosed (γ '' Icc 0 (2 * π)) :=
    (isCompact_Icc.image hK.continuous).isClosed
  intro z₀ hz₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosedImg.isOpen_compl z₀ hz₀
  have hfar : ∀ z ∈ ball z₀ (ε / 2), ∀ θ ∈ Icc 0 (2 * π), ε / 2 ≤ ‖γ θ - z‖ := by
    intro z hz θ hθ
    have h1 : ε ≤ ‖γ θ - z₀‖ := by
      by_contra h
      push_neg at h
      exact hball (mem_ball_iff_norm.mpr h) (mem_image_of_mem γ hθ)
    have h2 : ‖z - z₀‖ < ε / 2 := mem_ball_iff_norm.mp hz
    calc ε / 2 = ε - ε / 2 := by ring
      _ ≤ ‖γ θ - z₀‖ - ‖z - z₀‖ := by linarith
      _ ≤ ‖γ θ - z‖ := by
          have := norm_sub_norm_le (γ θ - z₀) (z - z₀)
          rw [show γ θ - z₀ - (z - z₀) = γ θ - z by ring] at this
          linarith
  refine ContinuousAt.continuousWithinAt ?_
  unfold windingNumber
  refine continuousAt_const.mul ?_
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => K / (ε / 2))
    ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun z => ((measurable_deriv γ).div
      (hK.continuous.measurable.sub measurable_const)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds z₀ (half_pos hε)] with z hz
    refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hpi] at hθ
    rw [norm_div]
    exact div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK θ) (half_pos hε)
      (hfar z hz θ ⟨hθ.1.le, hθ.2⟩)
  · refine Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le hpi] at hθ
    have hne : γ θ - z₀ ≠ 0 := by
      intro h
      have := hfar z₀ (mem_ball_self (half_pos hε)) θ ⟨hθ.1.le, hθ.2⟩
      rw [h, norm_zero] at this
      linarith
    exact continuousAt_const.div (continuousAt_const.sub continuousAt_id) hne

/-- `|wind(γ, z)| ≤ K / dist(z, γ)`: if every point of the curve is at distance at least
`d > K` from `z`, the winding number is `0` (for a closed curve). -/
theorem windingNumber_eq_zero_of_far {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {z : ℂ} {d : ℝ} (hd : (K : ℝ) < d)
    (hzd : ∀ θ ∈ Icc 0 (2 * π), d ≤ ‖γ θ - z‖) : windingNumber γ z = 0 := by
  have hd0 : 0 < d := lt_of_le_of_lt K.coe_nonneg hd
  have hz : z ∉ γ '' Icc 0 (2 * π) := by
    rintro ⟨θ, hθ, rfl⟩
    have := hzd θ hθ
    rw [sub_self, norm_zero] at this
    linarith
  obtain ⟨n, hn⟩ := windingNumber_mem_range_intCast hK hclosed hz
  have hbound : ‖windingNumber γ z‖ < 1 := by
    have hint : ‖∫ θ in (0 : ℝ)..(2 * π), deriv γ θ / (γ θ - z)‖ ≤ K / d * |2 * π - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
      rw [uIoc_of_le (by positivity)] at hθ
      have h1 := hzd θ ⟨hθ.1.le, hθ.2⟩
      rw [norm_div]
      exact div_le_div₀ K.coe_nonneg (norm_deriv_le_of_lipschitzWith hK θ) hd0 h1
    rw [windingNumber, norm_mul, norm_inv]
    have h2pi : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    rw [h2pi, sub_zero, abs_of_pos (by positivity)] at *
    calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * π), deriv γ θ / (γ θ - z)‖
        ≤ (2 * π)⁻¹ * (K / d * (2 * π)) := by gcongr
      _ = K / d := by field_simp
      _ < 1 := (div_lt_one hd0).mpr hd
  rw [← hn] at hbound ⊢
  have : |(n : ℝ)| < 1 := by
    rwa [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] at hbound
  have h1 : |n| < 1 := by
    rw [← Int.cast_abs] at this; exact_mod_cast this
  have : n = 0 := abs_eq_zero.mp (le_antisymm (by omega) (abs_nonneg n))
  rw [this, Int.cast_zero]

lemma isometry_intCast_complex : Isometry ((↑) : ℤ → ℂ) := by
  refine Isometry.of_dist_eq fun m n => ?_
  rw [Complex.dist_eq, Int.dist_eq, ← Complex.ofReal_intCast, ← Complex.ofReal_intCast,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

instance : DiscreteTopology (range ((↑) : ℤ → ℂ)) :=
  isometry_intCast_complex.isEmbedding.toHomeomorph.symm.isEmbedding.discreteTopology

/-- The winding number of a closed Lipschitz curve is constant on every preconnected set
avoiding the curve. -/
theorem windingNumber_const_of_isPreconnected {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) {S : Set ℂ} (hS : IsPreconnected S)
    (hSγ : Disjoint S (γ '' Icc 0 (2 * π))) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    windingNumber γ z = windingNumber γ w := by
  have hsub : S ⊆ (γ '' Icc 0 (2 * π))ᶜ := fun x hx h => disjoint_left.mp hSγ hx h
  exact hS.constant_of_mapsTo (isDiscrete_iff_discreteTopology.mpr inferInstance)
    ((continuousOn_windingNumber hK).mono hsub)
    (fun x hx => windingNumber_mem_range_intCast hK hclosed (hsub hx)) hz hw

end PolyaNeumann

end
