module

public import Theorem12Proof.ModularSixTransforms
import Mathlib.Tactic

/-!
# Uniform modular cusp limits

For each modular transformation, one of the coordinates `λ`, `1 - λ`, or
`1 / λ` tends to zero as the imaginary part of the input tends to infinity.
The result is uniform in the real part and is suited to approaching rational
Farey vertices from within the constructed domain.
-/

@[expose] public section

open Complex UpperHalfPlane NoWanderingDomains Filter
open scoped MatrixGroups ModularForm Manifold Topology

namespace ThreeOmittedValues

noncomputable def cuspNormalize (k : Fin 6) (z : ℂ) : ℂ :=
  ![z, 1 - z, z, 1 - z, z⁻¹, z⁻¹] k

noncomputable def normalizedLambdaTransform (k : Fin 6) (z : ℂ) : ℂ :=
  ![z, z, z / (z - 1), z / (z - 1), z / (z - 1), z] k

theorem cuspNormalize_lambdaTransform (k : Fin 6) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    cuspNormalize k (lambdaTransform k z) = normalizedLambdaTransform k z := by
  fin_cases k <;>
    simp [cuspNormalize, lambdaTransform, normalizedLambdaTransform] <;>
    field_simp [hz0, sub_ne_zero.mpr hz1, sub_ne_zero.mpr hz1.symm] <;> ring

theorem modularLambdaH_tendsto_zero_of_im_atTop {α : Type*} {l : Filter α}
    (T : α → UpperHalfPlane) (hT : Tendsto (fun a => (T a : ℂ).im) l atTop) :
    Tendsto (fun a => modularLambdaH (T a : ℂ)) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ a in l,
      ‖modularLambdaH (T a : ℂ)‖ ≤ 160000 * Real.exp (-Real.pi * (T a : ℂ).im) := by
    filter_upwards [hT.eventually (eventually_ge_atTop (1 : ℝ))] with a ha
    exact modularLambdaH_norm_le_exp_of_im_ge_one ha
  have harg : Tendsto (fun a => -Real.pi * (T a : ℂ).im) l atBot := by
    simpa using hT.const_mul_atTop_of_neg (show -Real.pi < 0 by linarith [Real.pi_pos])
  have hexp : Tendsto (fun a => 160000 * Real.exp (-Real.pi * (T a : ℂ).im)) l (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp harg).const_mul (160000 : ℝ)
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hbound hexp

theorem modularLambdaH_normalized_cusp_limit_of_formula {α : Type*} {l : Filter α}
    (γ : SL(2, ℤ)) (k : Fin 6)
    (hk : ∀ τ : UpperHalfPlane,
      modularLambdaH ((γ • τ : UpperHalfPlane) : ℂ) = lambdaTransform k (modularLambdaH (τ : ℂ))) :
    ∀ T : α → UpperHalfPlane,
      Tendsto (fun a => (T a : ℂ).im) l atTop →
      Tendsto (fun a => cuspNormalize k (modularLambdaH ((γ • T a : UpperHalfPlane) : ℂ)))
        l (𝓝 0) := by
  intro T hT
  have hsmall := modularLambdaH_tendsto_zero_of_im_atTop T hT
  have hratio : Tendsto (fun a => modularLambdaH (T a : ℂ) /
      (modularLambdaH (T a : ℂ) - 1)) l (𝓝 0) := by
    have hden : Tendsto (fun a => modularLambdaH (T a : ℂ) - 1) l (𝓝 (-1)) := by
      simpa using hsmall.sub_const 1
    simpa only [Pi.div_apply, zero_div] using!
      hsmall.div hden (by norm_num : (-1 : ℂ) ≠ 0)
  have heq : (fun a => cuspNormalize k (modularLambdaH ((γ • T a : UpperHalfPlane) : ℂ))) =
      (fun a => normalizedLambdaTransform k (modularLambdaH (T a : ℂ))) := by
    funext a
    rw [hk (T a)]
    exact cuspNormalize_lambdaTransform k
      (modularLambdaH_ne_zero (show 0 < (T a : ℂ).im from (T a).im_pos))
      (modularLambdaH_ne_one (show 0 < (T a : ℂ).im from (T a).im_pos))
  rw [heq]
  fin_cases k <;> simp only [normalizedLambdaTransform, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue] <;> assumption

theorem modularLambdaH_normalized_cusp_limit {α : Type*} {l : Filter α}
    (γ : SL(2, ℤ)) :
    ∃ k : Fin 6, ∀ T : α → UpperHalfPlane,
      Tendsto (fun a => (T a : ℂ).im) l atTop →
      Tendsto (fun a => cuspNormalize k (modularLambdaH ((γ • T a : UpperHalfPlane) : ℂ)))
        l (𝓝 0) := by
  obtain ⟨k, hk⟩ := modularLambdaH_six_transforms γ
  exact ⟨k, modularLambdaH_normalized_cusp_limit_of_formula γ k hk⟩

end ThreeOmittedValues
