module

public import Mathlib.Analysis.Calculus.Rademacher
public import Theorem12Proof.RequestProject.BasePoint

/-!
# Reparametrization invariance of the transport (Lemma 10.3, first assertion)

An orientation-preserving Lipschitz change of parameter `τ` with `τ 0 = 0`, `τ L = L`
does not change the endpoint value `V_E = W_E(L)` of the transport.  More precisely, if `W`
is the transport of `γ` then `W ∘ τ` is the transport of `γ ∘ τ`.

The proof follows the paper: the absolutely continuous chain rule and uniqueness.  The only
measure-theoretic input beyond Mathlib's one-dimensional area formula is that a monotone
function has vanishing derivative almost everywhere on the preimage of a null set
(`ae_deriv_eq_zero_of_preimage_null`).
-/

@[expose] public section

open MeasureTheory Set Filter Asymptotics
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- If a monotone function takes the same value at `a < x`, its derivative at `x` vanishes. -/
lemma monotone_deriv_eq_zero_of_eq_left {τ : ℝ → ℝ} (hm : Monotone τ) {a x : ℝ} (hax : a < x)
    (h : τ a = τ x) : deriv τ x = 0 := by
  by_cases hd : DifferentiableAt ℝ τ x
  · have h1 : HasDerivWithinAt τ 0 (Icc a x) x :=
      (hasDerivWithinAt_const x _ (τ x)).congr (fun y hy => le_antisymm (hm hy.2) (h ▸ hm hy.1))
        rfl
    exact (uniqueDiffOn_Icc hax x ⟨hax.le, le_rfl⟩).eq_deriv _
      hd.hasDerivAt.hasDerivWithinAt h1
  · exact deriv_zero_of_not_differentiableAt hd

/-- If a monotone function takes the same value at `x < b`, its derivative at `x` vanishes. -/
lemma monotone_deriv_eq_zero_of_eq_right {τ : ℝ → ℝ} (hm : Monotone τ) {x b : ℝ} (hxb : x < b)
    (h : τ x = τ b) : deriv τ x = 0 := by
  by_cases hd : DifferentiableAt ℝ τ x
  · have h1 : HasDerivWithinAt τ 0 (Icc x b) x :=
      (hasDerivWithinAt_const x _ (τ x)).congr
        (fun y hy => le_antisymm (h ▸ hm hy.2) (hm hy.1)) rfl
    exact (uniqueDiffOn_Icc hxb x ⟨le_rfl, hxb.le⟩).eq_deriv _
      hd.hasDerivAt.hasDerivWithinAt h1
  · exact deriv_zero_of_not_differentiableAt hd

/-- A monotone function has vanishing derivative at almost every point which it maps into a
given null set. -/
theorem ae_deriv_eq_zero_of_preimage_null {τ : ℝ → ℝ} (hm : Monotone τ) {N : Set ℝ}
    (hN : volume N = 0) : ∀ᵐ s, τ s ∈ N → deriv τ s = 0 := by
  set N' := toMeasurable volume N
  have hN' : volume N' = 0 := by rw [measure_toMeasurable]; exact hN
  set S := {s | DifferentiableAt ℝ τ s} ∩ ({s | deriv τ s ≠ 0} ∩ τ ⁻¹' N')
  have hS : MeasurableSet S :=
    (measurableSet_of_differentiableAt ℝ τ).inter
      (((measurable_deriv τ) (measurableSet_singleton 0)).compl.inter
        (hm.measurable (measurableSet_toMeasurable _ _)))
  have hinj : InjOn τ S := by
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hx.2.1 (monotone_deriv_eq_zero_of_eq_right hm h hxy)
    · exact hy.2.1 (monotone_deriv_eq_zero_of_eq_right hm h hxy.symm)
  have hder : ∀ x ∈ S, HasDerivWithinAt τ (deriv τ x) S x :=
    fun x hx => hx.1.hasDerivAt.hasDerivWithinAt
  have himg := lintegral_image_eq_lintegral_abs_deriv_mul hS hder hinj (fun _ => 1)
  have hsub : τ '' S ⊆ N' := by
    rintro _ ⟨x, hx, rfl⟩; exact hx.2.2
  have h0 : ∫⁻ x in S, ENNReal.ofReal |deriv τ x| * 1 = 0 := by
    rw [← himg]
    simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact measure_mono_null hsub hN'
  rw [lintegral_eq_zero_iff (by fun_prop)] at h0
  have h1 := (ae_restrict_iff' hS).mp h0
  have hτd : ∀ᵐ s, s ∉ S := by
    filter_upwards [h1] with x hx hxS
    have := hx hxS
    simp only [mul_one, Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
    exact hxS.2.1 (abs_nonpos_iff.mp this)
  filter_upwards [hτd] with s hs hsN
  by_contra hne
  by_cases hd : DifferentiableAt ℝ τ s
  · exact hs ⟨hd, hne, subset_toMeasurable _ _ hsN⟩
  · exact hne (deriv_zero_of_not_differentiableAt hd)

/-- Composition of a function which is Lipschitz on a set `S` with a function having
derivative zero and mapping a neighbourhood into `S` has derivative zero. -/
lemma hasDerivAt_comp_zero_of_lipschitzOnWith {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℝ → F} {τ : ℝ → ℝ} {S : Set ℝ} {K : NNReal} {x : ℝ}
    (hg : LipschitzOnWith K g S) (hτ : HasDerivAt τ 0 x) (hmap : ∀ᶠ y in 𝓝 x, τ y ∈ S) :
    HasDerivAt (fun y => g (τ y)) 0 x := by
  have hx : τ x ∈ S := hmap.self_of_nhds
  rw [hasDerivAt_iff_isLittleO] at hτ ⊢
  simp only [smul_zero, sub_zero] at hτ ⊢
  refine IsBigO.trans_isLittleO ?_ hτ
  refine IsBigO.of_bound K ?_
  filter_upwards [hmap] with y hy
  rw [← dist_eq_norm, Real.norm_eq_abs, ← Real.dist_eq]
  exact hg.dist_le_mul _ hy _ hx

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {C : ℝ → A} {M L L' : ℝ} {W : ℝ → A} {τ : ℝ → ℝ}

/-- Reparametrization of a linear Volterra equation: if `W` solves
`W(θ) = 1 + ∫₀^θ C W` on `[0, L]` and `τ` is monotone, Lipschitz, `τ 0 = 0`, `τ L' = L`, then
`W ∘ τ` solves the equation with coefficient `τ' · (C ∘ τ)` on `[0, L']`. -/
theorem volterra_reparam (hC : StronglyMeasurable C) (hM : ∀ s, ‖C s‖ ≤ M)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s)
    (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ) (h0 : τ 0 = 0) (hL : τ L' = L) :
    ∀ s ∈ Icc 0 L', W (τ s) = 1 + ∫ u in (0 : ℝ)..s, (deriv τ u • C (τ u)) * W (τ u) := by
  intro s hs
  have hmap : MapsTo τ (Icc 0 L') (Icc 0 L) := fun x hx => ⟨h0 ▸ hm hx.1, hL ▸ hm hx.2⟩
  obtain ⟨KW, hKW⟩ := volterra_lipschitzOn hC.aestronglyMeasurable hM hW eW
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  have hf : LipschitzOnWith (KW * Kτ) (fun u => W (τ u)) (Icc 0 L') :=
    hKW.comp hτ.lipschitzOnWith hmap
  have hWτ : ContinuousOn (fun u => W (τ u)) (Icc 0 L') := hW.comp hτ.continuous.continuousOn hmap
  have hgB : ∀ x ∈ Icc 0 L', ‖(deriv τ x • C (τ x)) * W (τ x)‖ ≤ Kτ * M * S := by
    intro x hx
    refine (norm_mul_le _ _).trans ?_
    rw [norm_smul]
    have h1 : ‖deriv τ x‖ ≤ Kτ := norm_deriv_le_of_lipschitz hτ
    have h2 := hM (τ x)
    have h3 := hS _ (hmap hx)
    have : 0 ≤ M := (norm_nonneg _).trans h2
    gcongr
  have hg : IntegrableOn (fun x => (deriv τ x • C (τ x)) * W (τ x)) (Icc 0 L') := by
    refine Integrable.of_bound ?_ (Kτ * M * S) ?_
    · exact ((measurable_deriv τ).aestronglyMeasurable.smul
        (hC.comp_measurable hm.measurable).aestronglyMeasurable).restrict.mul
        (hWτ.aestronglyMeasurable measurableSet_Icc)
    · exact (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hgB)
  have hN := ae_iff.mp (volterra_ae_hasDerivAt hC.aestronglyMeasurable hM hW eW)
  have hd : ∀ᵐ x, x ∈ Ioo 0 L' →
      HasDerivAt (fun u => W (τ u)) ((deriv τ x • C (τ x)) * W (τ x)) x := by
    filter_upwards [hτ.ae_differentiableAt, ae_deriv_eq_zero_of_preimage_null hm hN]
      with x hxd hxN hx
    by_cases hz : deriv τ x = 0
    · have h1 : HasDerivAt τ 0 x := hz ▸ hxd.hasDerivAt
      have := hasDerivAt_comp_zero_of_lipschitzOnWith hKW h1
        (by filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
            exact hmap (Ioo_subset_Icc_self hy))
      simpa [hz] using this
    · have hτx : τ x ∈ Ioo 0 L :=
        ⟨lt_of_le_of_ne (h0 ▸ hm hx.1.le)
          (fun h => hz (monotone_deriv_eq_zero_of_eq_left hm hx.1 (h0.trans h))),
         lt_of_le_of_ne (hL ▸ hm hx.2.le)
          (fun h => hz (monotone_deriv_eq_zero_of_eq_right hm hx.2 (h.trans hL.symm)))⟩
      have hWd : HasDerivAt W (C (τ x) * W (τ x)) (τ x) := by
        by_contra hc
        exact hz (hxN fun h => hc (h hτx))
      have := hWd.scomp x hxd.hasDerivAt
      rw [smul_mul_assoc]
      exact this
  have key := eq_add_integral_of_ae_hasDerivAt hf hg hgB hd s hs
  have hW0 : W 0 = 1 := by
    have h00 : (0 : ℝ) ∈ Icc 0 L := by
      have := hmap ⟨le_rfl, hs.1.trans hs.2⟩; rwa [h0] at this
    simpa using eW 0 h00
  simpa [h0, hW0] using key

/-- The almost-everywhere chain rule for a Lipschitz curve composed with a monotone Lipschitz
change of parameter. -/
theorem ae_deriv_comp {γ : ℝ → ℂ} {K : NNReal} (hγ : LipschitzWith K γ) {τ : ℝ → ℝ}
    (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ) :
    ∀ᵐ s, deriv (γ ∘ τ) s = ((deriv τ s : ℝ) : ℂ) * deriv γ (τ s) := by
  have hN := ae_iff.mp (hγ.ae_differentiableAt (μ := volume))
  filter_upwards [hτ.ae_differentiableAt, ae_deriv_eq_zero_of_preimage_null hm hN]
    with s hsd hsN
  by_cases hz : deriv τ s = 0
  · have := hasDerivAt_comp_zero_of_lipschitzOnWith (hγ.lipschitzOnWith (s := univ))
      (hz ▸ hsd.hasDerivAt) (Eventually.of_forall fun _ => mem_univ _)
    rw [show (γ ∘ τ) = fun y => γ (τ y) from rfl, this.deriv, hz]
    simp
  · have hγd : DifferentiableAt ℝ γ (τ s) := by
      by_contra h
      exact hz (hsN h)
    rw [(hγd.hasDerivAt.scomp s hsd.hasDerivAt).deriv, Complex.real_smul]

/-- The transport coefficient of a reparametrized curve. -/
lemma transportCoeff_comp_of_deriv {γ : ℝ → ℂ} {τ : ℝ → ℝ} {E s : ℝ}
    (h : deriv (γ ∘ τ) s = ((deriv τ s : ℝ) : ℂ) * deriv γ (τ s)) :
    transportCoeff (γ ∘ τ) E s = deriv τ s • transportCoeff γ E (τ s) := by
  unfold transportCoeff
  rw [h]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_smul,
    smul_add, smul_smul, smul_assoc, map_mul, Complex.conj_ofReal,
    mul_assoc, mul_left_comm, mul_comm]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

lemma transportCoeff_stronglyMeasurable (γ : ℝ → ℂ) (E : ℝ) :
    StronglyMeasurable (transportCoeff γ E) := by
  have hg : Continuous fun z : ℂ => (-(Complex.I * (Real.sqrt E : ℂ)) / 2) •
      (z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN) := by
    have : Continuous fun z : ℂ => conj z := Complex.continuous_conj
    fun_prop
  exact hg.comp_stronglyMeasurable (measurable_deriv γ).stronglyMeasurable

/-- Lemma 10.3 (reparametrization): if `W` is the transport of a Lipschitz curve `γ` and
`τ` is a monotone Lipschitz change of parameter with `τ 0 = 0` and `τ L = L`, then `W ∘ τ` is
the transport of `γ ∘ τ`. -/
theorem isTransport_comp {γ : ℝ → ℂ} {K : NNReal} (hγ : LipschitzWith K γ) {τ : ℝ → ℝ}
    (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ) (h0 : τ 0 = 0)
    (hL : τ (2 * π) = 2 * π) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) :
    IsTransport (γ ∘ τ) E (W ∘ τ) := by
  have hmap : MapsTo τ (Icc 0 (2 * π)) (Icc 0 (2 * π)) :=
    fun x hx => ⟨h0 ▸ hm hx.1, hL ▸ hm hx.2⟩
  refine ⟨hW.1.comp hτ.continuous.continuousOn hmap, fun s hs => ?_⟩
  rw [Function.comp_apply, volterra_reparam (transportCoeff_stronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hγ) hW.1 hW.2 hm hτ h0 hL s hs]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_deriv_comp hγ hm hτ] with u hu _
  rw [transportCoeff_comp_of_deriv hu, Function.comp_apply]
  rfl

/-- Lemma 10.3 (reparametrization): an orientation-preserving Lipschitz change of parameter
fixing the endpoints does not change the monodromy. -/
theorem monodromy_comp {γ : ℝ → ℂ} {K : NNReal} (hγ : LipschitzWith K γ) {τ : ℝ → ℝ}
    (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ) (h0 : τ 0 = 0)
    (hL : τ (2 * π) = 2 * π) {E : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (hW' : IsTransport (γ ∘ τ) E W') : monodromy W' = monodromy W := by
  have h := transport_unique_of_lipschitz (γ ∘ τ) (hγ.comp hτ) E hW'
    (isTransport_comp hγ hm hτ h0 hL hW) ⟨by positivity, le_rfl⟩
  unfold monodromy
  rw [h, Function.comp_apply, hL]

end PolyaNeumann

end
