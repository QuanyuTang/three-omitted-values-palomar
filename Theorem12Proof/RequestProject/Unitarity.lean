module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Theorem12Proof.RequestProject.Picard

/-!
# Unitarity of solutions of skew-adjoint linear Volterra equations

If `C : ℝ → A` is a bounded strongly measurable coefficient with values in a complete normed
star algebra and `C(s)^* = -C(s)`, then every continuous solution of
`W(θ) = 1 + ∫₀^θ C(s) W(s) ds` on `[0, L]` is unitary.  This is the unitarity part of
Lemma 10.2 of the paper.

The proof goes through the almost-everywhere derivative of the solution, using the
Lebesgue differentiation theorem for Banach-valued functions and the fact that an absolutely
continuous function with vanishing a.e. derivative is constant.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace PolyaNeumann

/-- The interval version of the Lebesgue differentiation theorem for Banach-valued
functions: if `f` is locally integrable then, for almost every `x` and every `c`,
`x ↦ ∫_c^x f` has derivative `f x` at `x`. -/
theorem ae_hasDerivAt_integral_of_locallyIntegrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun x => ∫ t in c..x, f t) (f x) x := by
  have hg (x y : ℝ) : IntervalIntegrable f volume x y :=
    intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have LDT := (IsUnifLocDoublingMeasure.vitaliFamily volume 1).ae_tendsto_average hf
  have {a b : ℝ} : ∫ (t : ℝ) in Ioc a b, f t = ∫ (t : ℝ) in Icc a b, f t :=
    integral_Icc_eq_integral_Ioc (x := a) (y := b) (X := ℝ) |>.symm
  filter_upwards [LDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_left)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : y ≤ x := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_ge, hy, this]
    rw [← neg_smul, ← inv_neg, neg_sub]
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_right)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : x ≤ y := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_le, hy, this]

/-- Integral form of an a.e. derivative: a Lipschitz function on `[0, L]` whose a.e.
derivative is a bounded integrable `g` is `f 0 + ∫₀^θ g`. -/
theorem eq_add_integral_of_ae_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} {L B : ℝ} {K : NNReal}
    (hf : LipschitzOnWith K f (Icc 0 L)) (hg : IntegrableOn g (Icc 0 L))
    (hgB : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ B)
    (hd : ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt f (g x) x) :
    ∀ θ ∈ Icc 0 L, f θ = f 0 + ∫ s in (0 : ℝ)..θ, g s := by
  set G : ℝ → E := (Icc 0 L).indicator g
  have hGi : Integrable G := hg.integrable_indicator measurableSet_Icc
  have hGB : ∀ x, ‖G x‖ ≤ max B 0 := fun x => by
    by_cases hx : x ∈ Icc 0 L
    · simp only [G, indicator_of_mem hx]; exact le_max_of_le_left (hgB x hx)
    · simp [G, indicator_of_notMem hx]
  set F : ℝ → E := fun x => ∫ t in (0 : ℝ)..x, G t
  have hFL : LipschitzOnWith (max B 0).toNNReal F (Icc 0 L) := by
    refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
    rw [dist_eq_norm, Real.coe_toNNReal _ (le_max_right _ _), Real.dist_eq]
    simp only [F]
    rw [intervalIntegral.integral_interval_sub_left hGi.intervalIntegrable
      hGi.intervalIntegrable]
    exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hGB t)
  have hFeq : ∀ θ ∈ Icc 0 L, F θ = ∫ t in (0 : ℝ)..θ, g t := fun θ hθ =>
    intervalIntegral.integral_congr fun t ht => by
      have : t ∈ Icc 0 L := by rw [uIcc_of_le hθ.1] at ht; exact ⟨ht.1, ht.2.trans hθ.2⟩
      simp [G, indicator_of_mem this]
  rcases lt_or_ge L 0 with hL | hL
  · intro θ hθ; exact absurd (hθ.1.trans hθ.2) (not_le.mpr hL)
  have hac : AbsolutelyContinuousOnInterval (f - F) 0 L := by
    rw [← uIcc_of_le hL] at hf hFL
    exact hf.absolutelyContinuousOnInterval.sub hFL.absolutelyContinuousOnInterval
  have hder : ∀ᵐ x, x ∈ uIcc 0 L → HasDerivAt (f - F) 0 x := by
    have h₁ : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff, measure_singleton]
    have h₂ : ∀ᵐ x : ℝ, x ≠ L := by simp [ae_iff, measure_singleton]
    filter_upwards [hd, ae_hasDerivAt_integral_of_locallyIntegrable hGi.locallyIntegrable,
      h₁, h₂] with x hx hxF hx0 hxL hxI
    rw [uIcc_of_le hL] at hxI
    have hxI' : x ∈ Ioo 0 L :=
      ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0), lt_of_le_of_ne hxI.2 hxL⟩
    have := (hx hxI').sub (hxF 0)
    simpa [G, indicator_of_mem hxI] using this
  obtain ⟨c, hc⟩ := hac.const_of_ae_hasDerivAt_zero hder
  intro θ hθ
  have h0 := hc 0 (by rw [uIcc_of_le hL]; exact ⟨le_rfl, hL⟩)
  have hθ' := hc θ (by rw [uIcc_of_le hL]; exact hθ)
  simp only [Pi.sub_apply, F, intervalIntegral.integral_same, sub_zero] at h0 hθ'
  rw [← hFeq θ hθ, h0, ← hθ']
  simp only [F]
  abel

/-- A Grönwall-type lemma: if `‖D θ‖ ≤ ∫₀^θ K ‖D‖` on `[0, L]` then `D = 0` there. -/
theorem eq_zero_of_norm_le_integral {E : Type*} [NormedAddCommGroup E] {D : ℝ → E}
    {L K : ℝ} (hK : 0 ≤ K) (hD : ContinuousOn D (Icc 0 L))
    (h : ∀ θ ∈ Icc 0 L, ‖D θ‖ ≤ ∫ s in (0 : ℝ)..θ, K * ‖D s‖) :
    ∀ θ ∈ Icc 0 L, D θ = 0 := by
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have hbound : ∀ n : ℕ, ∀ θ ∈ Icc 0 L, ‖D θ‖ ≤ S * (K * θ) ^ n / n.factorial := by
    intro n
    induction n with
    | zero => intro θ hθ; simpa using hS θ hθ
    | succ n ih =>
      intro θ hθ
      refine (h θ hθ).trans ?_
      have hsub : uIcc 0 θ ⊆ Icc 0 L := by
        rw [uIcc_of_le hθ.1]; exact Icc_subset_Icc le_rfl hθ.2
      have hint1 : IntervalIntegrable (fun s => K * ‖D s‖) volume 0 θ :=
        ContinuousOn.intervalIntegrable (continuousOn_const.mul (hD.mono hsub).norm)
      have hint2 : IntervalIntegrable
          (fun s => K * (S * (K * s) ^ n / n.factorial)) volume 0 θ := by
        apply Continuous.intervalIntegrable; fun_prop
      refine (intervalIntegral.integral_mono_on hθ.1 hint1 hint2 fun s hs => ?_).trans_eq ?_
      · exact mul_le_mul_of_nonneg_left (ih s ⟨hs.1, hs.2.trans hθ.2⟩) hK
      · have : (fun s : ℝ => K * (S * (K * s) ^ n / n.factorial)) =
            fun s => (K * S * K ^ n / n.factorial) * s ^ n := by
          funext s; rw [mul_pow]; ring
        rw [this, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
        push_cast
        field_simp
        ring
  intro θ hθ
  have hlim : Filter.Tendsto (fun n : ℕ => S * (K * θ) ^ n / n.factorial) Filter.atTop
      (nhds 0) := by
    have := (FloorSemiring.tendsto_pow_div_factorial_atTop (K * θ)).const_mul S
    simpa [mul_div_assoc] using this
  have h0 : ‖D θ‖ ≤ 0 := ge_of_tendsto' hlim fun n => hbound n θ hθ
  exact norm_le_zero_iff.mp h0

/-- A product of bounded Lipschitz functions is Lipschitz. -/
theorem lipschitzOnWith_mul_of_bounded {A : Type*} [NormedRing A] {f g : ℝ → A}
    {s : Set ℝ} {Kf Kg : NNReal} {B : ℝ} (hf : LipschitzOnWith Kf f s)
    (hg : LipschitzOnWith Kg g s) (hfB : ∀ x ∈ s, ‖f x‖ ≤ B) (hgB : ∀ x ∈ s, ‖g x‖ ≤ B) :
    LipschitzOnWith (Kf * B.toNNReal + B.toNNReal * Kg) (fun x => f x * g x) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hB : 0 ≤ B := (norm_nonneg _).trans (hfB x hx)
  have h1 := hf.dist_le_mul x hx y hy
  have h2 := hg.dist_le_mul x hx y hy
  rw [dist_eq_norm] at h1 h2 ⊢
  have e : f x * g x - f y * g y = (f x - f y) * g x + f y * (g x - g y) := by noncomm_ring
  rw [e]
  push_cast
  rw [Real.coe_toNNReal _ hB]
  calc ‖(f x - f y) * g x + f y * (g x - g y)‖
      ≤ ‖f x - f y‖ * ‖g x‖ + ‖f y‖ * ‖g x - g y‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ (Kf * dist x y) * B + B * (Kg * dist x y) := by
        gcongr
        · exact hgB x hx
        · exact hfB y hy
    _ = _ := by ring

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {C : ℝ → A} {M L : ℝ} {W : ℝ → A}

/-- A solution of the Volterra equation has a.e. derivative `C W` in `(0, L)`. -/
theorem volterra_ae_hasDerivAt (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s) :
    ∀ᵐ θ, θ ∈ Ioo 0 L → HasDerivAt W (C θ * W θ) θ := by
  rcases lt_or_ge L 0 with hL | hL
  · exact Filter.Eventually.of_forall fun θ hθ =>
      absurd (hθ.1.trans hθ.2) (not_lt.mpr hL.le)
  set g : ℝ → A := (Icc 0 L).indicator (fun s => C s * W s)
  have hgi : Integrable g := by
    have h1 := intervalIntegrable_mul_of_continuousOn hC hM hW (θ := L) ⟨hL, le_rfl⟩
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL,
      ← integrableOn_Icc_iff_integrableOn_Ioc] at h1
    exact h1.integrable_indicator measurableSet_Icc
  filter_upwards [ae_hasDerivAt_integral_of_locallyIntegrable hgi.locallyIntegrable]
    with θ hθ hmem
  have hmem' : θ ∈ Icc 0 L := Ioo_subset_Icc_self hmem
  have h1 := (hθ 0).const_add (1 : A)
  rw [show g θ = C θ * W θ by simp [g, indicator_of_mem hmem']] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with x hx
  rw [eW x (Ioo_subset_Icc_self hx)]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  have : t ∈ Icc 0 L := by rw [uIcc_of_le hx.1.le] at ht; exact ⟨ht.1, ht.2.trans hx.2.le⟩
  simp [g, indicator_of_mem this]

omit [CompleteSpace A] in
/-- A solution of the Volterra equation is Lipschitz on `[0, L]`. -/
theorem volterra_lipschitzOn (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s) :
    ∃ K, LipschitzOnWith K W (Icc 0 L) := by
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨(M * max S 0).toNNReal, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  rw [dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hM0 (le_max_right _ _)), Real.dist_eq,
    eW x hx, eW y hy, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_mul_of_continuousOn hC hM hW hx)
      (intervalIntegrable_mul_of_continuousOn hC hM hW hy)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
  have : t ∈ Icc 0 L := by
    have := uIoc_subset_uIcc ht
    rw [mem_uIcc] at this
    rcases this with h | h
    · exact ⟨hy.1.trans h.1, h.2.trans hx.2⟩
    · exact ⟨hx.1.trans h.1, h.2.trans hy.2⟩
  exact (norm_mul_le _ _).trans
    (mul_le_mul (hM t) ((hS t this).trans (le_max_left _ _)) (norm_nonneg _) hM0)

variable [StarRing A] [StarModule ℝ A] [NormedStarGroup A]

/-- Unitarity for skew-adjoint linear Volterra equations. -/
theorem volterra_unitary (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hskew : ∀ s, star (C s) = -C s) (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s) :
    ∀ θ ∈ Icc 0 L, star (W θ) * W θ = 1 ∧ W θ * star (W θ) = 1 := by
  rcases lt_or_ge L 0 with hL | hL
  · intro θ hθ; exact absurd (hθ.1.trans hθ.2) (not_le.mpr hL)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hW0 : W 0 = 1 := by simpa using eW 0 ⟨le_rfl, hL⟩
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0 ⟨le_rfl, hL⟩)
  obtain ⟨K, hK⟩ := volterra_lipschitzOn hC hM hW eW
  have hKs : LipschitzOnWith K (fun θ => star (W θ)) (Icc 0 L) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [dist_eq_norm, ← star_sub, norm_star, ← dist_eq_norm]
      exact hK.dist_le_mul x hx y hy
  have hSs : ∀ x ∈ Icc 0 L, ‖star (W x)‖ ≤ S := fun x hx => by rw [norm_star]; exact hS x hx
  have hd := volterra_ae_hasDerivAt hC hM hW eW
  have hds : ∀ᵐ θ, θ ∈ Ioo 0 L →
      HasDerivAt (fun θ => star (W θ)) (-(star (W θ) * C θ)) θ := by
    filter_upwards [hd] with θ hθ hmem
    have := (hθ hmem).star
    rwa [star_mul, hskew, mul_neg] at this
  intro θ hθ
  constructor
  · have hP := eq_add_integral_of_ae_hasDerivAt (g := fun _ => (0 : A)) (B := 0)
      (lipschitzOnWith_mul_of_bounded hKs hK hSs hS) integrableOn_zero
      (fun _ _ => by simp) (by
        filter_upwards [hd, hds] with θ h1 h2 hmem
        have := (h2 hmem).mul (h1 hmem)
        convert this using 1
        noncomm_ring)
    simpa [hW0] using hP θ hθ
  · set Q : ℝ → A := fun θ => W θ * star (W θ)
    have hQc : ContinuousOn Q (Icc 0 L) := hW.mul hW.star
    have hQB : ∀ x ∈ Icc 0 L, ‖Q x‖ ≤ S * S := fun x hx =>
      (norm_mul_le _ _).trans (mul_le_mul (hS x hx) (hSs x hx) (norm_nonneg _) hS0)
    set g : ℝ → A := fun s => C s * Q s - Q s * C s
    have hgm : AEStronglyMeasurable g (volume.restrict (Icc 0 L)) :=
      (hC.restrict.mul (hQc.aestronglyMeasurable measurableSet_Icc)).sub
        ((hQc.aestronglyMeasurable measurableSet_Icc).mul hC.restrict)
    have hgB : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ 2 * M * (S * S) := fun x hx => by
      calc ‖g x‖ ≤ ‖C x * Q x‖ + ‖Q x * C x‖ := norm_sub_le _ _
        _ ≤ M * (S * S) + (S * S) * M :=
          add_le_add
            ((norm_mul_le _ _).trans (mul_le_mul (hM x) (hQB x hx) (norm_nonneg _) hM0))
            ((norm_mul_le _ _).trans
              (mul_le_mul (hQB x hx) (hM x) (norm_nonneg _) (mul_nonneg hS0 hS0)))
        _ = _ := by ring
    have hgi : IntegrableOn g (Icc 0 L) :=
      Integrable.of_bound hgm (2 * M * (S * S))
        ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hgB))
    have hQ := eq_add_integral_of_ae_hasDerivAt (lipschitzOnWith_mul_of_bounded hK hKs hS hSs)
      hgi hgB (by
        filter_upwards [hd, hds] with θ h1 h2 hmem
        have := (h1 hmem).mul (h2 hmem)
        convert this using 1
        simp only [g, Q]
        noncomm_ring)
    set D : ℝ → A := fun θ => Q θ - 1
    have hDc : ContinuousOn D (Icc 0 L) := hQc.sub continuousOn_const
    have hDeq : ∀ θ ∈ Icc 0 L, D θ = ∫ s in (0 : ℝ)..θ, g s := fun θ hθ => by
      simp only [D, Q]; rw [hQ θ hθ, hW0, star_one, one_mul, add_sub_cancel_left]
    have hgD : ∀ s, ‖g s‖ ≤ 2 * M * ‖D s‖ := fun s => by
      have : g s = C s * D s - D s * C s := by simp only [g, D]; noncomm_ring
      rw [this]
      calc ‖C s * D s - D s * C s‖ ≤ ‖C s * D s‖ + ‖D s * C s‖ := norm_sub_le _ _
        _ ≤ M * ‖D s‖ + ‖D s‖ * M :=
          add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hM s) (norm_nonneg _)))
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hM s) (norm_nonneg _)))
        _ = _ := by ring
    have hD0 := eq_zero_of_norm_le_integral (K := 2 * M) (by positivity) hDc (fun θ hθ => by
      rw [hDeq θ hθ]
      refine (intervalIntegral.norm_integral_le_integral_norm hθ.1).trans ?_
      have hsub : uIcc 0 θ ⊆ Icc 0 L := by
        rw [uIcc_of_le hθ.1]; exact Icc_subset_Icc le_rfl hθ.2
      refine intervalIntegral.integral_mono_on hθ.1 ?_ ?_ fun s _ => hgD s
      · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hθ.1).mpr
          (hgi.mono_set (Icc_subset_Icc le_rfl hθ.2))).norm
      · exact ContinuousOn.intervalIntegrable (continuousOn_const.mul (hDc.mono hsub).norm))
    exact sub_eq_zero.mp (hD0 θ hθ)

end PolyaNeumann

end
