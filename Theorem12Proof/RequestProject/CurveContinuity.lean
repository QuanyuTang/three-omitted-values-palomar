module

public import Mathlib.Analysis.Calculus.Rademacher
public import Theorem12Proof.RequestProject.Observation

/-!
# Continuity of the monodromy under uniform convergence of curves (Lemma 10.6)

If closed Lipschitz curves `γₙ` converge uniformly to a closed Lipschitz curve `γ` with
uniformly bounded lengths `∫₀^L |γₙ'|`, and `Eₙ → E`, then `U_{γₙ}(Eₙ) → U_γ(E)` in operator
norm.

The proof is the paper's: with `Fₙ` a primitive of `C - Cₙ` vanishing at both endpoints,
the variation identity and an integration by parts give
`Vₙ^* V - I = ∫₀^L Wₙ^* (Cₙ Fₙ - Fₙ C) W`, whence
`‖Vₙ^* V - I‖ ≤ ‖Fₙ‖_∞ ∫₀^L (‖Cₙ‖ + ‖C‖) → 0`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

section Generic

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A] [StarModule ℝ A] [NormedStarGroup A]
variable {C C' : ℝ → A} {M M' L : ℝ} {W W' F : ℝ → A}

/-- A bounded strongly measurable function is interval integrable. -/
lemma intervalIntegrable_of_bounded {G : Type*} [NormedAddCommGroup G] {f : ℝ → G}
    (hf : AEStronglyMeasurable f volume) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ => B) intervalIntegrable_const hf.restrict
    (Eventually.of_forall hB)

/-- The variation identity with an integration by parts, at every point of `[0, L]`: if
`F' = C - C'` almost everywhere and `F(0) = 0`, then
`W'(θ)^* W(θ) - 1 = W'(θ)^* F(θ) W(θ) + ∫₀^θ W'^* (C' F - F C) W`. -/
theorem volterra_variation_at (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s)
    (hC' : AEStronglyMeasurable C' volume) (hM' : ∀ s, ‖C' s‖ ≤ M')
    (hskew' : ∀ s, star (C' s) = -C' s) (hW' : ContinuousOn W' (Icc 0 L))
    (eW' : ∀ θ ∈ Icc 0 L, W' θ = 1 + ∫ s in (0 : ℝ)..θ, C' s * W' s)
    (hL : 0 ≤ L) {KF : NNReal} (hF : LipschitzOnWith KF F (Icc 0 L))
    (hFd : ∀ᵐ θ, θ ∈ Ioo 0 L → HasDerivAt F (C θ - C' θ) θ) (hF0 : F 0 = 0) :
    ∀ θ ∈ Icc 0 L, star (W' θ) * W θ - 1 = star (W' θ) * F θ * W θ +
      ∫ s in (0 : ℝ)..θ, star (W' s) * (C' s * F s - F s * C s) * W s := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM0' : 0 ≤ M' := (norm_nonneg _).trans (hM' 0)
  have hW0 : W 0 = 1 := by simpa using eW 0 ⟨le_rfl, hL⟩
  have hW0' : W' 0 = 1 := by simpa using eW' 0 ⟨le_rfl, hL⟩
  have hFc : ContinuousOn F (Icc 0 L) := hF.continuousOn
  obtain ⟨S1, hS1⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  obtain ⟨S2, hS2⟩ := isCompact_Icc.exists_bound_of_continuousOn hW'
  obtain ⟨S3, hS3⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL⟩
  have hS1' : 0 ≤ S1 := (norm_nonneg _).trans (hS1 0 h0)
  have hS2' : 0 ≤ S2 := (norm_nonneg _).trans (hS2 0 h0)
  have hS3' : 0 ≤ S3 := (norm_nonneg _).trans (hS3 0 h0)
  set B : ℝ := (1 + S1 + S2 + S3) * (1 + S1 + S2 + S3) with hB
  have hB1 : 1 + S1 + S2 + S3 ≤ B := by nlinarith
  have hb1 : ∀ x ∈ Icc 0 L, ‖W x‖ ≤ B := fun x hx => by linarith [hS1 x hx]
  have hb2 : ∀ x ∈ Icc 0 L, ‖star (W' x)‖ ≤ B := fun x hx => by
    rw [norm_star]; linarith [hS2 x hx]
  have hb3 : ∀ x ∈ Icc 0 L, ‖F x‖ ≤ B := fun x hx => by linarith [hS3 x hx]
  have hb23 : ∀ x ∈ Icc 0 L, ‖star (W' x) * F x‖ ≤ B := fun x hx => by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_star]
    calc ‖W' x‖ * ‖F x‖ ≤ (1 + S1 + S2 + S3) * (1 + S1 + S2 + S3) :=
          mul_le_mul (by linarith [hS2 x hx]) (by linarith [hS3 x hx]) (norm_nonneg _)
            (by linarith)
      _ = B := rfl
  obtain ⟨K1, hK1⟩ := volterra_lipschitzOn hC hM hW eW
  obtain ⟨K2, hK2⟩ := volterra_lipschitzOn hC' hM' hW' eW'
  have hK2s : LipschitzOnWith K2 (fun θ => star (W' θ)) (Icc 0 L) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [dist_eq_norm, ← star_sub, norm_star, ← dist_eq_norm]
      exact hK2.dist_le_mul x hx y hy
  have hd := volterra_ae_hasDerivAt hC hM hW eW
  have hd' := volterra_ae_hasDerivAt hC' hM' hW' eW'
  have hds : ∀ᵐ θ, θ ∈ Ioo 0 L →
      HasDerivAt (fun θ => star (W' θ)) (-(star (W' θ) * C' θ)) θ := by
    filter_upwards [hd'] with θ hθ hmem
    have := (hθ hmem).star
    rwa [star_mul, hskew', mul_neg] at this
  set G : ℝ → A := fun θ => star (W' θ) * W θ - star (W' θ) * F θ * W θ with hG
  have hGL : LipschitzOnWith _ G (Icc 0 L) :=
    (lipschitzOnWith_mul_of_bounded hK2s hK1 hb2 hb1).sub
      (lipschitzOnWith_mul_of_bounded (lipschitzOnWith_mul_of_bounded hK2s hF hb2 hb3) hK1
        hb23 hb1)
  set g : ℝ → A := fun s => star (W' s) * (C' s * F s - F s * C s) * W s with hg
  have hgm : AEStronglyMeasurable g (volume.restrict (Icc 0 L)) :=
    (((hW'.star).aestronglyMeasurable measurableSet_Icc).mul
      ((hC'.restrict.mul (hFc.aestronglyMeasurable measurableSet_Icc)).sub
        ((hFc.aestronglyMeasurable measurableSet_Icc).mul hC.restrict))).mul
      (hW.aestronglyMeasurable measurableSet_Icc)
  have hgB : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ B * (M' * B + B * M) * B := fun x hx => by
    have hB0 : 0 ≤ B := by positivity
    calc ‖g x‖ ≤ ‖star (W' x)‖ * ‖C' x * F x - F x * C x‖ * ‖W x‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ B * (M' * B + B * M) * B := by
          gcongr
          · exact hb2 x hx
          · refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
            · exact (norm_mul_le _ _).trans (mul_le_mul (hM' x) (hb3 x hx) (norm_nonneg _) hM0')
            · exact (norm_mul_le _ _).trans (mul_le_mul (hb3 x hx) (hM x) (norm_nonneg _) hB0)
          · exact hb1 x hx
  have hgi : IntegrableOn g (Icc 0 L) :=
    Integrable.of_bound hgm (B * (M' * B + B * M) * B)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hgB))
  have hP := eq_add_integral_of_ae_hasDerivAt hGL hgi hgB (by
    filter_upwards [hd, hds, hFd] with θ h1 h2 h3 hmem
    have := ((h2 hmem).mul (h1 hmem)).sub (((h2 hmem).mul (h3 hmem)).mul (h1 hmem))
    convert this using 1
    simp only [g, Pi.mul_apply]
    noncomm_ring)
  intro θ hθ
  have := hP θ hθ
  simp only [hG, hW0, hW0', hF0, star_one, one_mul, mul_zero, zero_mul, sub_zero] at this
  calc star (W' θ) * W θ - 1
      = (star (W' θ) * W θ - star (W' θ) * F θ * W θ) + star (W' θ) * F θ * W θ - 1 := by abel
    _ = _ := by rw [this]; abel

/-- The variation identity with an integration by parts: if `F' = C - C'` almost
everywhere and `F(0) = F(L) = 0`, then
`W'(L)^* W(L) - 1 = ∫₀^L W'^* (C' F - F C) W`. -/
theorem volterra_variation (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s)
    (hC' : AEStronglyMeasurable C' volume) (hM' : ∀ s, ‖C' s‖ ≤ M')
    (hskew' : ∀ s, star (C' s) = -C' s) (hW' : ContinuousOn W' (Icc 0 L))
    (eW' : ∀ θ ∈ Icc 0 L, W' θ = 1 + ∫ s in (0 : ℝ)..θ, C' s * W' s)
    (hL : 0 ≤ L) {KF : NNReal} (hF : LipschitzOnWith KF F (Icc 0 L))
    (hFd : ∀ᵐ θ, θ ∈ Ioo 0 L → HasDerivAt F (C θ - C' θ) θ) (hF0 : F 0 = 0) (hFL : F L = 0) :
    star (W' L) * W L - 1 = ∫ s in (0 : ℝ)..L, star (W' s) * (C' s * F s - F s * C s) * W s := by
  rw [volterra_variation_at hC hM hW eW hC' hM' hskew' hW' eW' hL hF hFd hF0 L ⟨hL, le_rfl⟩,
    hFL, mul_zero, zero_mul, zero_add]

omit [CompleteSpace A] [StarModule ℝ A] [NormedStarGroup A] in
/-- The norm estimate in the variation identity. -/
theorem norm_volterra_variation_le (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (hC' : AEStronglyMeasurable C' volume) (hM' : ∀ s, ‖C' s‖ ≤ M') (hL : 0 ≤ L)
    {ε : ℝ} (hFε : ∀ θ ∈ Icc 0 L, ‖F θ‖ ≤ ε) (hWn : ∀ θ ∈ Icc 0 L, ‖W θ‖ ≤ 1)
    (hW'n : ∀ θ ∈ Icc 0 L, ‖star (W' θ)‖ ≤ 1) :
    ‖∫ s in (0 : ℝ)..L, star (W' s) * (C' s * F s - F s * C s) * W s‖ ≤
      ε * ∫ s in (0 : ℝ)..L, (‖C' s‖ + ‖C s‖) := by
  have hi : IntervalIntegrable (fun s => ‖C' s‖ + ‖C s‖) volume 0 L :=
    intervalIntegrable_of_bounded (hC'.norm.add hC.norm)
      (B := M' + M) (fun s => by
        show ‖‖C' s‖ + ‖C s‖‖ ≤ M' + M
        rw [Real.norm_of_nonneg (by positivity)]; exact add_le_add (hM' s) (hM s)) 0 L
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le hL
    (Eventually.of_forall fun t ht => ?_) (hi.const_mul ε)
  have ht' : t ∈ Icc 0 L := Ioc_subset_Icc_self ht
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hFε t ht')
  calc ‖star (W' t) * (C' t * F t - F t * C t) * W t‖
      ≤ ‖star (W' t)‖ * ‖C' t * F t - F t * C t‖ * ‖W t‖ := by
        refine (norm_mul_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ 1 * (‖C' t‖ * ε + ε * ‖C t‖) * 1 := by
        gcongr
        · exact hW'n t ht'
        · refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
          · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hFε t ht') (norm_nonneg _))
          · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hFε t ht') (norm_nonneg _))
        · exact hWn t ht'
    _ = ε * (‖C' t‖ + ‖C t‖) := by ring

end Generic

/-! ### The boundary transport -/

/-- The matrix `-(i √E / 2) (z S_N^* + conj(z) S_N)`; the transport coefficient is
`C_E(θ) = coeffOf E (γ'(θ))`. -/
def coeffOf (E : ℝ) (z : ℂ) : Ell2 →L[ℂ] Ell2 :=
  (-(Complex.I * (Real.sqrt E : ℂ)) / 2) •
    (z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN)

lemma transportCoeff_eq_coeffOf (γ : ℝ → ℂ) (E θ : ℝ) :
    transportCoeff γ E θ = coeffOf E (deriv γ θ) := rfl

/-- The constant `κ = (‖S_N^*‖ + ‖S_N‖) / 2`. -/
def shiftConst : ℝ := (‖(ContinuousLinearMap.adjoint shiftN : Ell2 →L[ℂ] Ell2)‖ + ‖shiftN‖) / 2

lemma shiftConst_nonneg : 0 ≤ shiftConst := by unfold shiftConst; positivity

lemma coeffOf_sub (E : ℝ) (z w : ℂ) : coeffOf E z - coeffOf E w = coeffOf E (z - w) := by
  unfold coeffOf
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, map_sub, smul_sub, sub_smul, smul_add, smul_smul]
  module

lemma coeffOf_zero (E : ℝ) : coeffOf E 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp [coeffOf]

lemma norm_I_mul_div_two (r : ℝ) : ‖(-(Complex.I * (r : ℂ)) / 2)‖ = |r| / 2 := by
  rw [norm_div, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  simp

lemma norm_shiftPart_le (z : ℂ) :
    ‖z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN‖ ≤ 2 * shiftConst * ‖z‖ := by
  unfold shiftConst
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Complex.norm_conj]
  linarith

lemma norm_coeffOf_le (E : ℝ) (z : ℂ) : ‖coeffOf E z‖ ≤ Real.sqrt E * shiftConst * ‖z‖ := by
  unfold coeffOf
  rw [norm_smul, norm_I_mul_div_two, abs_of_nonneg (Real.sqrt_nonneg E)]
  calc Real.sqrt E / 2 * ‖z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN‖
      ≤ Real.sqrt E / 2 * (2 * shiftConst * ‖z‖) := by
        gcongr; exact norm_shiftPart_le z
    _ = _ := by ring

lemma norm_coeffOf_sub_coeffOf_le (E E' : ℝ) (z : ℂ) :
    ‖coeffOf E z - coeffOf E' z‖ ≤ |Real.sqrt E - Real.sqrt E'| * shiftConst * ‖z‖ := by
  unfold coeffOf
  let P : Ell2 →L[ℂ] Ell2 := z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN
  change ‖(-(Complex.I * (Real.sqrt E : ℂ)) / 2) • P -
      (-(Complex.I * (Real.sqrt E' : ℂ)) / 2) • P‖ ≤ _
  rw [(sub_smul _ _ P).symm, show -(Complex.I * (Real.sqrt E : ℂ)) / 2 - -(Complex.I * (Real.sqrt E' : ℂ)) / 2
      = -(Complex.I * ((Real.sqrt E - Real.sqrt E' : ℝ) : ℂ)) / 2 by push_cast; ring,
    norm_smul, norm_I_mul_div_two]
  calc |Real.sqrt E - Real.sqrt E'| / 2 *
        ‖z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN‖
      ≤ |Real.sqrt E - Real.sqrt E'| / 2 * (2 * shiftConst * ‖z‖) := by
        gcongr; exact norm_shiftPart_le z
    _ = _ := by ring

lemma hasDerivAt_coeffOf {γ : ℝ → ℂ} {γ' : ℂ} {θ : ℝ} (h : HasDerivAt γ γ' θ) (E : ℝ) (c : ℂ) :
    HasDerivAt (fun θ => coeffOf E (γ θ - c)) (coeffOf E γ') θ := by
  have h1 := h.sub_const c
  have h2 : HasDerivAt (fun θ => conj (γ θ - c)) (conj γ') θ := h1.star
  exact ((h1.smul_const (ContinuousLinearMap.adjoint shiftN)).add
    (h2.smul_const shiftN)).const_smul (-(Complex.I * (Real.sqrt E : ℂ)) / 2)

lemma lipschitzWith_coeffOf {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (E : ℝ) (c : ℂ) :
    LipschitzWith (Real.sqrt E * shiftConst * K).toNNReal (fun θ => coeffOf E (γ θ - c)) := by
  refine LipschitzWith.of_dist_le' fun x y => ?_
  rw [dist_eq_norm, coeffOf_sub, sub_sub_sub_cancel_right]
  refine (norm_coeffOf_le E _).trans ?_
  rw [mul_assoc _ (K : ℝ)]
  have := hK.dist_le_mul x y
  rw [dist_eq_norm] at this
  have h0 : 0 ≤ Real.sqrt E * shiftConst := mul_nonneg (Real.sqrt_nonneg E) shiftConst_nonneg
  exact mul_le_mul_of_nonneg_left this h0

/-- Unitary operators have norm at most one. -/
lemma norm_le_one_of_mem_unitary {U : Ell2 →L[ℂ] Ell2} (hU : U ∈ unitary (Ell2 →L[ℂ] Ell2)) :
    ‖U‖ ≤ 1 := by
  have h1 := CStarRing.norm_coe_unitary_mul (⟨U, hU⟩ : unitary (Ell2 →L[ℂ] Ell2)) 1
  simp only [mul_one] at h1
  rw [h1]
  exact ContinuousLinearMap.norm_id_le

lemma norm_coeffOf_sub_coeffOf_le' (E E' : ℝ) (z z' : ℂ) :
    ‖coeffOf E z - coeffOf E' z'‖ ≤
      |Real.sqrt E - Real.sqrt E'| * shiftConst * ‖z‖ + Real.sqrt E' * shiftConst * ‖z - z'‖ := by
  have : coeffOf E z - coeffOf E' z' = (coeffOf E z - coeffOf E' z) + coeffOf E' (z - z') := by
    rw [← coeffOf_sub]; abel
  rw [this]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_coeffOf_sub_coeffOf_le E E' z) (norm_coeffOf_le E' _))

lemma integral_norm_transportCoeff_le {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (E : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), ‖transportCoeff γ E θ‖ ≤
      Real.sqrt E * shiftConst * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv γ θ‖ := by
  rw [← intervalIntegral.integral_const_mul]
  have hd : ∀ s, ‖deriv γ s‖ ≤ K := fun s => norm_deriv_le_of_lipschitz hK
  refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ fun θ _ => ?_
  · exact intervalIntegrable_of_bounded (transportCoeff_aestronglyMeasurable γ E).norm
      (fun s => by rw [norm_norm]; exact transportCoeff_norm_le γ E hK s) _ _
  · refine (intervalIntegrable_of_bounded (measurable_deriv γ).aestronglyMeasurable.norm
      (B := K) (fun s => by rw [norm_norm]; exact hd s) _ _).const_mul _
  · exact norm_coeffOf_le E _

/-- The values of the transport of a Lipschitz curve are unitary. -/
lemma transport_mem_unitary {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    W θ ∈ unitary (Ell2 →L[ℂ] Ell2) :=
  Unitary.mem_iff.mpr (volterra_unitary (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) (transportCoeff_star γ E) hW.1 hW.2 θ hθ)

/-- The variation identity for two transports, with the explicit primitive
`F = coeffOf E (γ - γ(0)) - coeffOf E' (γ' - γ'(0))` of `C - C'`, and the resulting
estimate `‖V'^* V - I‖ ≤ ε ∫₀^L (‖C'‖ + ‖C‖)` whenever `‖F‖ ≤ ε` on `[0, L]`. -/
theorem norm_transport_variation_le {γ γ' : ℝ → ℂ} {K K' : NNReal} (hK : LipschitzWith K γ)
    (hK' : LipschitzWith K' γ') (hclosed : γ (2 * π) = γ 0) (hclosed' : γ' (2 * π) = γ' 0)
    {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (hW' : IsTransport γ' E' W') {ε : ℝ}
    (hε : ∀ θ ∈ Icc 0 (2 * π),
      ‖coeffOf E (γ θ - γ 0) - coeffOf E' (γ' θ - γ' 0)‖ ≤ ε) :
    ‖star (W' (2 * π)) * W (2 * π) - 1‖ ≤
      ε * ∫ s in (0 : ℝ)..(2 * π), (‖transportCoeff γ' E' s‖ + ‖transportCoeff γ E s‖) := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  set F : ℝ → Ell2 →L[ℂ] Ell2 := fun θ => coeffOf E (γ θ - γ 0) - coeffOf E' (γ' θ - γ' 0)
    with hF
  have hFL : LipschitzOnWith _ F (Icc 0 (2 * π)) :=
    ((lipschitzWith_coeffOf hK E (γ 0)).sub (lipschitzWith_coeffOf hK' E' (γ' 0))).lipschitzOnWith
  have hFd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * π) →
      HasDerivAt F (transportCoeff γ E θ - transportCoeff γ' E' θ) θ := by
    filter_upwards [hK.ae_differentiableAt (μ := volume),
      hK'.ae_differentiableAt (μ := volume)] with θ h1 h2 _
    exact (hasDerivAt_coeffOf h1.hasDerivAt E (γ 0)).sub
      (hasDerivAt_coeffOf h2.hasDerivAt E' (γ' 0))
  have hF0 : F 0 = 0 := by simp [hF, coeffOf_zero]
  have hF2 : F (2 * π) = 0 := by simp [hF, hclosed, hclosed', coeffOf_zero]
  rw [volterra_variation (transportCoeff_aestronglyMeasurable γ E) (transportCoeff_norm_le γ E hK)
    hW.1 hW.2 (transportCoeff_aestronglyMeasurable γ' E') (transportCoeff_norm_le γ' E' hK')
    (transportCoeff_star γ' E') hW'.1 hW'.2 hπ hFL hFd hF0 hF2]
  refine norm_volterra_variation_le (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) (transportCoeff_aestronglyMeasurable γ' E')
    (transportCoeff_norm_le γ' E' hK') hπ hε
    (fun θ hθ => norm_le_one_of_mem_unitary (transport_mem_unitary hK hW hθ))
    (fun θ hθ => norm_le_one_of_mem_unitary
      (Unitary.star_mem (transport_mem_unitary hK' hW' hθ)))

/-- **Lemma 10.6 (continuity under uniform curve convergence).** Let `γₙ, γ` be closed
Lipschitz curves on `[0, L]` such that `γₙ → γ` uniformly on `[0, L]` and the lengths
`∫₀^L |γₙ'|` are uniformly bounded. If `Eₙ → E`, then `U_{γₙ}(Eₙ) → U_γ(E)` in operator
norm. -/
theorem monodromy_tendsto_of_tendstoUniformlyOn {γ : ℝ → ℂ} {γs : ℕ → ℝ → ℂ} {K : NNReal}
    {Ks : ℕ → NNReal} (hK : LipschitzWith K γ) (hKs : ∀ n, LipschitzWith (Ks n) (γs n))
    (hclosed : γ (2 * π) = γ 0) (hclosed' : ∀ n, γs n (2 * π) = γs n 0)
    (hunif : TendstoUniformlyOn γs γ atTop (Icc 0 (2 * π)))
    (hlen : ∃ B, ∀ n, ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (γs n) θ‖ ≤ B)
    {E : ℝ} {Es : ℕ → ℝ} (hE : Tendsto Es atTop (𝓝 E))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    {Ws : ℕ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ n, IsTransport (γs n) (Es n) (Ws n)) :
    Tendsto (fun n => monodromy (Ws n)) atTop (𝓝 (monodromy W)) := by
  obtain ⟨B, hB⟩ := hlen
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have h0mem : (0 : ℝ) ∈ Icc 0 (2 * π) := ⟨le_rfl, hπ⟩
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 (2 * π)) hK.continuous.continuousOn
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 h0mem)
  have hκ := shiftConst_nonneg
  set κ := shiftConst
  set s0 := Real.sqrt E with hs0
  have hs00 : 0 ≤ s0 := Real.sqrt_nonneg E
  set A0 := ∫ θ in (0 : ℝ)..(2 * π), ‖transportCoeff γ E θ‖ with hA0def
  have hA0 : 0 ≤ A0 := intervalIntegral.integral_nonneg hπ fun _ _ => norm_nonneg _
  set B' := max B 0
  have hB' : 0 ≤ B' := le_max_right _ _
  set c1 := 2 * κ * (R + s0 + 1) with hc1def
  set c2 := (s0 + 1) * κ * B' + A0 with hc2def
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hbound : ∀ n, ∀ η, 0 ≤ η → η ≤ 1 → |s0 - Real.sqrt (Es n)| ≤ η →
      (∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γs n θ‖ ≤ η) →
      ‖monodromy (Ws n) - monodromy W‖ ≤ η * c1 * c2 := by
    intro n η hη0 hη1 hηE hηγ
    have hsq : Real.sqrt (Es n) ≤ s0 + 1 := by
      have := (abs_le.mp hηE).1
      linarith
    have hε : ∀ θ ∈ Icc 0 (2 * π),
        ‖coeffOf E (γ θ - γ 0) - coeffOf (Es n) (γs n θ - γs n 0)‖ ≤ η * c1 := by
      intro θ hθ
      refine (norm_coeffOf_sub_coeffOf_le' _ _ _ _).trans ?_
      have h1 : ‖γ θ - γ 0‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith [hR θ hθ, hR 0 h0mem])
      have h2 : ‖(γ θ - γ 0) - (γs n θ - γs n 0)‖ ≤ 2 * η := by
        rw [show (γ θ - γ 0) - (γs n θ - γs n 0) = (γ θ - γs n θ) - (γ 0 - γs n 0) by ring]
        exact (norm_sub_le _ _).trans (by linarith [hηγ θ hθ, hηγ 0 h0mem])
      calc |s0 - Real.sqrt (Es n)| * κ * ‖γ θ - γ 0‖ +
            Real.sqrt (Es n) * κ * ‖(γ θ - γ 0) - (γs n θ - γs n 0)‖
          ≤ η * κ * (2 * R) + (s0 + 1) * κ * (2 * η) := by
            gcongr
        _ = η * c1 := by rw [hc1def]; ring
    have hvar := norm_transport_variation_le hK (hKs n) hclosed (hclosed' n) hW (hWs n) hε
    have hint : ∫ s in (0 : ℝ)..(2 * π),
        (‖transportCoeff (γs n) (Es n) s‖ + ‖transportCoeff γ E s‖) ≤ c2 := by
      rw [intervalIntegral.integral_add
        (intervalIntegrable_of_bounded (transportCoeff_aestronglyMeasurable _ _).norm
          (fun s => by rw [norm_norm]; exact transportCoeff_norm_le _ _ (hKs n) s) _ _)
        (intervalIntegrable_of_bounded (transportCoeff_aestronglyMeasurable _ _).norm
          (fun s => by rw [norm_norm]; exact transportCoeff_norm_le _ _ hK s) _ _)]
      have h3 := integral_norm_transportCoeff_le (hKs n) (Es n)
      have h4 : 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (γs n) θ‖ :=
        intervalIntegral.integral_nonneg hπ fun _ _ => norm_nonneg _
      have h5 : Real.sqrt (Es n) * κ * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (γs n) θ‖ ≤
          (s0 + 1) * κ * B' := by
        gcongr
        exact (hB n).trans (le_max_left _ _)
      rw [hc2def]
      linarith
    have hV := transport_mem_unitary hK hW (θ := 2 * π) ⟨hπ, le_rfl⟩
    have hVV : W (2 * π) * star (W (2 * π)) = 1 := (Unitary.mem_iff.mp hV).2
    have heq : monodromy (Ws n) - monodromy W =
        (star (Ws n (2 * π)) * W (2 * π) - 1) * star (W (2 * π)) := by
      unfold monodromy
      rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, sub_mul,
        mul_assoc, hVV, mul_one, one_mul]
    rw [heq]
    calc ‖(star (Ws n (2 * π)) * W (2 * π) - 1) * star (W (2 * π))‖
        ≤ ‖star (Ws n (2 * π)) * W (2 * π) - 1‖ * 1 :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
            (norm_le_one_of_mem_unitary (Unitary.star_mem hV)) (norm_nonneg _))
      _ ≤ η * c1 * c2 := by
          rw [mul_one]
          refine hvar.trans ?_
          exact mul_le_mul_of_nonneg_left hint (mul_nonneg hη0 hc1)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η := min 1 (ε / (2 * (c1 * c2 + 1))) with hηdef
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η * c1 * c2 < ε := by
    have h1 : η ≤ ε / (2 * (c1 * c2 + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [mul_nonneg hc1 hc2]
  have hsqrt : Tendsto (fun n => Real.sqrt (Es n)) atTop (𝓝 s0) :=
    (Real.continuous_sqrt.tendsto E).comp hE
  filter_upwards [Metric.tendsto_nhds.mp hsqrt η hηpos,
    Metric.tendstoUniformlyOn_iff.mp hunif η hηpos] with n hn1 hn2
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (hbound n η hηpos.le hη1 ?_ ?_) hηε
  · rw [Real.dist_eq] at hn1
    rw [abs_sub_comm]; exact hn1.le
  · intro θ hθ
    rw [← dist_eq_norm]; exact (hn2 θ hθ).le

end PolyaNeumann

end
