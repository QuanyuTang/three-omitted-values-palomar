module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Tactic

/-!
# Linear Volterra equations in a Banach algebra

For a bounded, strongly measurable coefficient `C : ℝ → A` with values in a complete
normed algebra `A`, the linear integral equation `W(θ) = 1 + ∫₀^θ C(s) W(s) ds` has a
continuous solution on `[0, L]`, given by the Picard (Dyson) series.  This is the
existence part of Lemmas 4.4 and 10.2 of the paper.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace PolyaNeumann

variable {A : Type*} [NormedRing A] [NormedSpace ℝ A] [CompleteSpace A]

/-- The Picard iterates (terms of the Dyson series). -/
def picardTerm (C : ℝ → A) : ℕ → ℝ → A
  | 0 => fun _ => 1
  | n + 1 => fun θ => ∫ s in (0 : ℝ)..θ, C s * picardTerm C n s

variable {C : ℝ → A} {M : ℝ}

omit [NormedSpace ℝ A] [CompleteSpace A] in
lemma picardTerm_intervalIntegrable (hC : AEStronglyMeasurable C volume)
    (hM : ∀ s, ‖C s‖ ≤ M) {p : ℝ → A} (hp : Continuous p) (a b : ℝ) :
    IntervalIntegrable (fun s => C s * p s) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun s => M * ‖p s‖)
    (by exact (continuous_const.mul hp.norm).intervalIntegrable a b)
    ((hC.mul hp.aestronglyMeasurable).restrict) ?_
  refine Filter.Eventually.of_forall fun s => ?_
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hM s) (norm_nonneg _))

omit [CompleteSpace A] in
lemma picardTerm_continuous (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M) :
    ∀ n, Continuous (picardTerm C n)
  | 0 => continuous_const
  | n + 1 => intervalIntegral.continuous_primitive
      (picardTerm_intervalIntegrable hC hM (picardTerm_continuous hC hM n)) 0

omit [CompleteSpace A] in
lemma picardTerm_bound (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M) :
    ∀ n θ, 0 ≤ θ → ‖picardTerm C n θ‖ ≤ ‖(1 : A)‖ * (M * θ) ^ n / n.factorial
  | 0, θ, _ => by simp [picardTerm]
  | n + 1, θ, hθ => by
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    simp only [picardTerm]
    refine (intervalIntegral.norm_integral_le_integral_norm hθ).trans ?_
    have hint1 : IntervalIntegrable (fun s => ‖C s * picardTerm C n s‖) volume 0 θ :=
      (picardTerm_intervalIntegrable hC hM (picardTerm_continuous hC hM n) 0 θ).norm
    have hint2 : IntervalIntegrable
        (fun s => M * (‖(1 : A)‖ * (M * s) ^ n / n.factorial)) volume 0 θ := by
      apply Continuous.intervalIntegrable; fun_prop
    refine (intervalIntegral.integral_mono_on hθ hint1 hint2 fun s hs => ?_).trans_eq ?_
    · refine (norm_mul_le _ _).trans (mul_le_mul (hM s) ?_ (norm_nonneg _) hM0)
      exact picardTerm_bound hC hM n s hs.1
    · have : (fun s : ℝ => M * (‖(1 : A)‖ * (M * s) ^ n / n.factorial)) =
          fun s => (M * ‖(1 : A)‖ * M ^ n / n.factorial) * s ^ n := by
        funext s; rw [mul_pow]; ring
      rw [this, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
      push_cast
      field_simp
      ring

omit [CompleteSpace A] in
lemma picardTerm_bound' (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (L : ℝ) (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 L) :
    ‖picardTerm C n θ‖ ≤ ‖(1 : A)‖ * (M * L) ^ n / n.factorial := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine (picardTerm_bound hC hM n θ hθ.1).trans ?_
  gcongr
  · exact mul_nonneg hM0 hθ.1
  · exact hθ.2

omit [NormedSpace ℝ A] [CompleteSpace A] in
lemma summable_picard_bound (L : ℝ) :
    Summable fun n : ℕ => ‖(1 : A)‖ * (M * L) ^ n / n.factorial := by
  simpa [mul_div_assoc] using (Real.summable_pow_div_factorial (M * L)).mul_left ‖(1 : A)‖

/-- Existence for the linear Volterra equation `W(θ) = 1 + ∫₀^θ C(s) W(s) ds` on `[0, L]`
with a bounded strongly measurable coefficient. -/
theorem exists_volterra_solution (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (L : ℝ) :
    ∃ W : ℝ → A, ContinuousOn W (Set.Icc 0 L) ∧
      ∀ θ ∈ Set.Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s := by
  set W : ℝ → A := fun θ => ∑' n, picardTerm C n θ
  have hsum : ∀ θ ∈ Set.Icc 0 L, HasSum (fun n => picardTerm C n θ) (W θ) := by
    intro θ hθ
    exact (Summable.of_norm_bounded (summable_picard_bound (A := A) (M := M) L)
      fun n => picardTerm_bound' hC hM L n θ hθ).hasSum
  refine ⟨W, continuousOn_tsum (fun n => (picardTerm_continuous hC hM n).continuousOn)
    (summable_picard_bound L) (fun n θ hθ => picardTerm_bound' hC hM L n θ hθ), ?_⟩
  intro θ hθ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hsub : Set.uIoc 0 θ ⊆ Set.Icc 0 L := by
    rw [Set.uIoc_of_le hθ.1]
    exact fun s hs => ⟨hs.1.le, hs.2.trans hθ.2⟩
  have key : HasSum (fun n => ∫ s in (0 : ℝ)..θ, C s * picardTerm C n s)
      (∫ s in (0 : ℝ)..θ, C s * W s) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => M * (‖(1 : A)‖ * (M * L) ^ n / n.factorial)) (fun n => ?_) (fun n => ?_)
      ?_ ?_ ?_
    · exact (hC.mul (picardTerm_continuous hC hM n).aestronglyMeasurable).restrict
    · refine Filter.Eventually.of_forall fun s hs => ?_
      exact (norm_mul_le _ _).trans
        (mul_le_mul (hM s) (picardTerm_bound' hC hM L n s (hsub hs)) (norm_nonneg _) hM0)
    · exact Filter.Eventually.of_forall fun s _ => (summable_picard_bound L).mul_left M
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun s hs => (hsum s (hsub hs)).mul_left (C s)
  have h2 : HasSum (fun n => picardTerm C (n + 1) θ) (W θ - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr (hsum θ hθ)
    simpa [picardTerm] using this
  have h3 := key.unique h2
  rw [h3]; abel

omit [NormedSpace ℝ A] [CompleteSpace A] in
lemma intervalIntegrable_mul_of_continuousOn (hC : AEStronglyMeasurable C volume)
    (hM : ∀ s, ‖C s‖ ≤ M) {L : ℝ} {p : ℝ → A} (hp : ContinuousOn p (Set.Icc 0 L)) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 L) : IntervalIntegrable (fun s => C s * p s) volume 0 θ := by
  have hsub : Set.uIcc 0 θ ⊆ Set.Icc 0 L := by
    rw [Set.uIcc_of_le hθ.1]; exact Set.Icc_subset_Icc le_rfl hθ.2
  refine IntervalIntegrable.mono_fun' (g := fun s => M * ‖p s‖)
    (ContinuousOn.intervalIntegrable ((continuousOn_const.mul (hp.mono hsub).norm)))
    (hC.restrict.mul ((hp.mono (Set.uIoc_subset_uIcc.trans hsub)).aestronglyMeasurable
      measurableSet_uIoc)) ?_
  refine Filter.Eventually.of_forall fun s => ?_
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hM s) (norm_nonneg _))

omit [CompleteSpace A] in
/-- Uniqueness for the linear Volterra equation on `[0, L]`. -/
theorem volterra_unique (hC : AEStronglyMeasurable C volume) (hM : ∀ s, ‖C s‖ ≤ M)
    (L : ℝ) {W W' : ℝ → A} (hW : ContinuousOn W (Set.Icc 0 L))
    (hW' : ContinuousOn W' (Set.Icc 0 L))
    (eW : ∀ θ ∈ Set.Icc 0 L, W θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W s)
    (eW' : ∀ θ ∈ Set.Icc 0 L, W' θ = 1 + ∫ s in (0 : ℝ)..θ, C s * W' s) :
    Set.EqOn W W' (Set.Icc 0 L) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set D : ℝ → A := fun θ => W θ - W' θ
  have hD : ContinuousOn D (Set.Icc 0 L) := hW.sub hW'
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have hS0 : ∀ θ ∈ Set.Icc 0 L, 0 ≤ S := fun θ hθ => (norm_nonneg _).trans (hS θ hθ)
  have hDeq : ∀ θ ∈ Set.Icc 0 L, D θ = ∫ s in (0 : ℝ)..θ, C s * D s := by
    intro θ hθ
    simp only [D, mul_sub]
    rw [intervalIntegral.integral_sub (intervalIntegrable_mul_of_continuousOn hC hM hW hθ)
      (intervalIntegrable_mul_of_continuousOn hC hM hW' hθ), eW θ hθ, eW' θ hθ]
    abel
  have hbound : ∀ n : ℕ, ∀ θ ∈ Set.Icc 0 L, ‖D θ‖ ≤ S * (M * θ) ^ n / n.factorial := by
    intro n
    induction n with
    | zero => intro θ hθ; simpa using hS θ hθ
    | succ n ih =>
      intro θ hθ
      rw [hDeq θ hθ]
      refine (intervalIntegral.norm_integral_le_integral_norm hθ.1).trans ?_
      have hint1 : IntervalIntegrable (fun s => ‖C s * D s‖) volume 0 θ :=
        (intervalIntegrable_mul_of_continuousOn hC hM hD hθ).norm
      have hint2 : IntervalIntegrable
          (fun s => M * (S * (M * s) ^ n / n.factorial)) volume 0 θ := by
        apply Continuous.intervalIntegrable; fun_prop
      refine (intervalIntegral.integral_mono_on hθ.1 hint1 hint2 fun s hs => ?_).trans_eq ?_
      · have hs' : s ∈ Set.Icc 0 L := ⟨hs.1, hs.2.trans hθ.2⟩
        exact (norm_mul_le _ _).trans (mul_le_mul (hM s) (ih s hs') (norm_nonneg _) hM0)
      · have : (fun s : ℝ => M * (S * (M * s) ^ n / n.factorial)) =
            fun s => (M * S * M ^ n / n.factorial) * s ^ n := by
          funext s; rw [mul_pow]; ring
        rw [this, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
        push_cast
        field_simp
        ring
  intro θ hθ
  have hlim : Filter.Tendsto (fun n : ℕ => S * (M * θ) ^ n / n.factorial) Filter.atTop
      (nhds 0) := by
    have := (FloorSemiring.tendsto_pow_div_factorial_atTop (M * θ)).const_mul S
    simpa [mul_div_assoc] using this
  have h0 : ‖D θ‖ ≤ 0 := ge_of_tendsto' hlim fun n => hbound n θ hθ
  have : D θ = 0 := norm_le_zero_iff.mp h0
  exact sub_eq_zero.mp this

end PolyaNeumann

end
