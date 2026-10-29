module

public import Theorem12Proof.RequestProject.BasePoint

/-!
# Injectivity of the observation map on Lipschitz curves (Lemma 10.4)

For a Lipschitz boundary curve with `γ' ≠ 0` almost everywhere and `E > 0`, the
observation map `O_E v = ⟨e₀, W_E(·) v⟩` is injective: if `⟨e₀, W_E(θ) v⟩ = 0` for all
`θ ∈ [0, L]`, then `v = 0`.

The proof follows the paper: writing `f = W_E v`, each row of the transport equation
expresses `f_n'` through `γ' f_{n+1}` and `conj(γ') f_{n-1}`; inductively all coordinates
of `f` vanish, and `v = f(0) = 0`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- If all primitives `∫₀^θ g`, `θ ∈ [0, L]`, of an interval integrable function vanish,
then `g = 0` almost everywhere on `(0, L)`. -/
lemma ae_eq_zero_of_primitive_eq_zero {g : ℝ → ℂ} {L : ℝ}
    (hg : IntervalIntegrable g volume 0 L)
    (h : ∀ θ ∈ Icc 0 L, ∫ s in (0 : ℝ)..θ, g s = 0) :
    ∀ᵐ s, s ∈ Ioo 0 L → g s = 0 := by
  rcases lt_or_ge L 0 with hL | hL
  · exact Filter.Eventually.of_forall fun s hs => absurd (hs.1.trans hs.2) (not_lt.mpr hL.le)
  set G := (Ioc 0 L).indicator g with hG
  have hGi : Integrable G volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mp hg)
  filter_upwards [ae_hasDerivAt_integral_of_locallyIntegrable hGi.locallyIntegrable] with x hx hxI
  have hF : (fun y => ∫ t in (0 : ℝ)..y, G t) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
    rw [← h y ⟨hy.1.le, hy.2.le⟩]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hy.1.le] at ht
    exact indicator_of_mem (show t ∈ Ioc 0 L from ⟨ht.1, ht.2.trans hy.2.le⟩) g
  have h0 : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, G t) 0 x :=
    (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hF
  have := (hx 0).unique h0
  rwa [hG, indicator_of_mem (Ioo_subset_Ioc_self hxI)] at this

/-- The `n`-th coordinate of `C_E(s) g`. -/
lemma transportCoeff_apply_coord (γ : ℝ → ℂ) (E s : ℝ) (g : Ell2) (n : ℕ) :
    (transportCoeff γ E s g : ℕ → ℂ) n =
      (-(Complex.I * (Real.sqrt E : ℂ)) / 2) *
        (deriv γ s * (shiftWeight n * (g : ℕ → ℂ) (n + 1)) +
          conj (deriv γ s) * (shiftN g : ℕ → ℂ) n) := by
  unfold transportCoeff
  rw [← shiftNAdj_eq_adjoint]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, lp.coeFn_smul,
    lp.coeFn_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul, shiftNAdj_apply]

/-- The rows of the transport equation, in integral form. -/
lemma transport_coord_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (v : Ell2) (n : ℕ)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    (W θ v : ℕ → ℂ) n = (v : ℕ → ℂ) n +
      ∫ s in (0 : ℝ)..θ, (transportCoeff γ E s (W s v) : ℕ → ℂ) n := by
  set Φ : (Ell2 →L[ℂ] Ell2) →L[ℂ] ℂ :=
    (innerSL ℂ (basisVec n)).comp (ContinuousLinearMap.apply ℂ Ell2 v) with hΦ
  have hΦa : ∀ X : Ell2 →L[ℂ] Ell2, Φ X = (X v : ℕ → ℂ) n := fun X => by
    simp [hΦ, basisVec, inner_single]
  have hint := intervalIntegrable_mul_of_continuousOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hθ
  rw [← hΦa, hW.2 θ hθ, map_add, hΦa, ← Φ.intervalIntegral_comp_comm hint]
  simp only [hΦa, ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply]

/-- The rows of the transport equation have integrable right-hand sides. -/
lemma transport_coord_intervalIntegrable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (v : Ell2) (n : ℕ) :
    IntervalIntegrable (fun s => (transportCoeff γ E s (W s v) : ℕ → ℂ) n) volume 0 (2 * π) := by
  set Φ : (Ell2 →L[ℂ] Ell2) →L[ℂ] ℂ :=
    (innerSL ℂ (basisVec n)).comp (ContinuousLinearMap.apply ℂ Ell2 v) with hΦ
  have hΦa : ∀ X : Ell2 →L[ℂ] Ell2, Φ X = (X v : ℕ → ℂ) n := fun X => by
    simp [hΦ, basisVec, inner_single]
  have hint := intervalIntegrable_mul_of_continuousOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 (θ := 2 * π) ⟨by positivity, le_rfl⟩
  have : IntervalIntegrable (fun s => Φ (transportCoeff γ E s * W s)) volume 0 (2 * π) :=
    ⟨Φ.integrable_comp hint.1, Φ.integrable_comp hint.2⟩
  simpa [hΦa] using this

/-- Lemma 10.4: injectivity of the observation map on a Lipschitz curve with nonvanishing
derivative. -/
theorem observation_injective {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hγ' : ∀ᵐ θ, deriv γ θ ≠ 0) {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (v : Ell2)
    (hv : ∀ θ ∈ Icc 0 (2 * π), inner ℂ (basisVec 0) (W θ v) = 0) : v = 0 := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  set f : ℕ → ℝ → ℂ := fun n θ => (W θ v : ℕ → ℂ) n with hf
  have hfi : ∀ n θ, f n θ = inner ℂ (basisVec n) (W θ v) := fun n θ => by
    simp [hf, basisVec, inner_single]
  have hcont : ∀ n, ContinuousOn (f n) (Icc 0 (2 * π)) := fun n => by
    have : ContinuousOn (fun θ => inner ℂ (basisVec n) (W θ v)) (Icc 0 (2 * π)) :=
      continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
    exact this.congr fun θ _ => hfi n θ
  have hW0 : W 0 = 1 := by simpa using hW.2 0 ⟨le_rfl, hπ⟩
  have hf0 : ∀ n, f n 0 = (v : ℕ → ℂ) n := fun n => by simp [hf, hW0]
  have ha : (-(Complex.I * (Real.sqrt E : ℂ)) / 2) ≠ 0 := by
    have : (Real.sqrt E : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hE).ne'
    simp [this, Complex.I_ne_zero]
  have hw : ∀ n, shiftWeight n ≠ 0 := fun n => by
    unfold shiftWeight; split_ifs <;> simp
  have step : ∀ n, (∀ θ ∈ Icc 0 (2 * π), f n θ = 0) →
      (∀ θ ∈ Icc 0 (2 * π), (shiftN (W θ v) : ℕ → ℂ) n = 0) →
      ∀ θ ∈ Icc 0 (2 * π), f (n + 1) θ = 0 := by
    intro n hn hS
    have hprim : ∀ θ ∈ Icc 0 (2 * π),
        ∫ s in (0 : ℝ)..θ, (transportCoeff γ E s (W s v) : ℕ → ℂ) n = 0 := by
      intro θ hθ
      have := transport_coord_eq hK hW v n hθ
      rw [← hf0 n] at this
      change f n θ = f n 0 + _ at this
      rw [hn θ hθ, hn 0 ⟨le_rfl, hπ⟩, zero_add] at this
      exact this.symm
    have hae := ae_eq_zero_of_primitive_eq_zero (transport_coord_intervalIntegrable hK hW v n)
      hprim
    have hae' : ∀ᵐ s, s ∈ Ioo 0 (2 * π) → f (n + 1) s = 0 := by
      filter_upwards [hae, hγ'] with s hs hs' hsI
      have h1 := hs hsI
      rw [transportCoeff_apply_coord, hS s (Ioo_subset_Icc_self hsI), mul_zero, add_zero] at h1
      simpa [ha, hs', hw n] using h1
    have hae'' : f (n + 1) =ᵐ[volume.restrict (Icc 0 (2 * π))] fun _ => (0 : ℂ) := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact (ae_restrict_iff' measurableSet_Ioo).mpr hae'
    exact Measure.eqOn_Icc_of_ae_eq volume (by positivity) hae'' (hcont (n + 1))
      continuousOn_const
  have key : ∀ n, (∀ θ ∈ Icc 0 (2 * π), f n θ = 0) ∧ (∀ θ ∈ Icc 0 (2 * π), f (n + 1) θ = 0) := by
    intro n
    induction n with
    | zero =>
      have h0 : ∀ θ ∈ Icc 0 (2 * π), f 0 θ = 0 := fun θ hθ => by rw [hfi]; exact hv θ hθ
      exact ⟨h0, step 0 h0 fun θ _ => shiftN_apply_zero _⟩
    | succ n ih =>
      refine ⟨ih.2, step (n + 1) ih.2 fun θ hθ => ?_⟩
      rw [shiftN_apply_succ]
      change shiftWeight n * f n θ = 0
      rw [ih.1 θ hθ, mul_zero]
  apply lp.ext
  funext n
  rw [← hf0 n, (key n).1 0 ⟨le_rfl, hπ⟩]
  rfl

/-- Lemma 10.4 for a boundary parametrization, with the observation `O_E v` vanishing in
`L²(0, L)`, i.e. almost everywhere on `[0, L]`: then `v = 0`. -/
theorem observation_injective_of_boundaryParam {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (v : Ell2)
    (hv : ∀ᵐ θ ∂(volume.restrict (Icc 0 (2 * π))), inner ℂ (basisVec 0) (W θ v) = 0) :
    v = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
  have hγ' : ∀ᵐ θ, deriv γ θ ≠ 0 := by
    filter_upwards [hspeed] with θ hθ h0
    rw [h0, norm_zero] at hθ
    exact hc.ne hθ
  refine observation_injective hK hγ' hE hW v ?_
  have hcont : ContinuousOn (fun θ => inner ℂ (basisVec 0) (W θ v)) (Icc 0 (2 * π)) :=
    continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
  exact Measure.eqOn_Icc_of_ae_eq volume (by positivity) hv hcont continuousOn_const

/-- Parseval for the first row of an operator:
`∑ₙ |⟨e₀, X eₙ⟩|² = ‖X^* e₀‖²`. -/
lemma hasSum_norm_inner_basisVec_sq (X : Ell2 →L[ℂ] Ell2) :
    HasSum (fun n => ‖inner ℂ (basisVec 0) (X (basisVec n))‖ ^ 2)
      (‖ContinuousLinearMap.adjoint X (basisVec 0)‖ ^ 2) := by
  set g := ContinuousLinearMap.adjoint X (basisVec 0)
  have h : ∀ n, ‖inner ℂ (basisVec 0) (X (basisVec n))‖ ^ 2 = ‖(g : ℕ → ℂ) n‖ ^ 2 := by
    intro n
    rw [← ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm, basisVec, inner_single,
      RCLike.norm_conj]
  simp_rw [h]
  rw [← tsum_sq_eq_norm_sq]
  exact (summable_sq g).hasSum

/-- `‖W^* e₀‖ = 1` for the values of the transport. -/
lemma norm_adjoint_transport_basisVec {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖ContinuousLinearMap.adjoint (W θ) (basisVec 0)‖ = 1 := by
  have h1 := transport_mul_adjoint hK hW hθ
  have h2 : ‖ContinuousLinearMap.adjoint (W θ) (basisVec 0)‖ ^ 2 = ‖basisVec 0‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.mul_apply, h1,
      ContinuousLinearMap.one_apply]
  have h3 : ‖basisVec 0‖ = 1 := by
    rw [basisVec, lp.norm_single (by norm_num)]; simp
  rw [h3, one_pow] at h2
  have := norm_nonneg (ContinuousLinearMap.adjoint (W θ) (basisVec 0))
  nlinarith

/-- Lemma 4.6 / Definition 10.1, the Hilbert–Schmidt identity `‖O_E‖²_{𝒮₂} = L`:
`∑ₙ ∫₀^L |⟨e₀, W_E(θ) eₙ⟩|² dθ = L`. -/
theorem observation_hilbertSchmidt {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) :
    HasSum (fun n => ∫ θ in (0 : ℝ)..(2 * π), ‖inner ℂ (basisVec 0) (W θ (basisVec n))‖ ^ 2)
      (2 * π) := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  set F : ℕ → ℝ → ℝ := fun n θ => ‖inner ℂ (basisVec 0) (W θ (basisVec n))‖ ^ 2 with hF
  set f : ℝ → ℝ := fun θ => ‖ContinuousLinearMap.adjoint (W θ) (basisVec 0)‖ ^ 2 with hf
  have hsum : ∀ θ, HasSum (fun n => F n θ) (f θ) := fun θ =>
    hasSum_norm_inner_basisVec_sq (W θ)
  have hsub : uIoc 0 (2 * π) ⊆ Icc 0 (2 * π) := by
    rw [uIoc_of_le hπ]; exact Ioc_subset_Icc_self
  have hFc : ∀ n, ContinuousOn (F n) (Icc 0 (2 * π)) := fun n =>
    ((continuousOn_const.inner (hW.1.clm_apply continuousOn_const)).norm).pow 2
  have hfc : ContinuousOn f (Icc 0 (2 * π)) :=
    ((ContinuousLinearMap.adjoint.continuous.comp_continuousOn hW.1).clm_apply
      continuousOn_const).norm.pow 2
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (f := f)
    (a := 0) (b := 2 * π) F (fun n => ((hFc n).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    (fun n => Filter.Eventually.of_forall fun t _ => by
      rw [Real.norm_of_nonneg (by positivity)])
    (Filter.Eventually.of_forall fun t _ => (hsum t).summable)
    (by
      have : (fun t => ∑' n, F n t) = f := funext fun t => (hsum t).tsum_eq
      rw [this]
      exact (hfc.mono (by rw [uIcc_of_le hπ])).intervalIntegrable)
    (Filter.Eventually.of_forall fun t _ => hsum t)
  have hint : ∫ θ in (0 : ℝ)..(2 * π), f θ = 2 * π := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun θ hθ => by
      rw [uIcc_of_le hπ] at hθ
      simp only [hf, norm_adjoint_transport_basisVec hK hW hθ, one_pow]]
    simp
  rw [hint] at key
  exact key

end PolyaNeumann

end
