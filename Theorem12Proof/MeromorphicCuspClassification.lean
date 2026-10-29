module

public import Theorem12Proof.MeromorphicFibres
public import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic

/-!
# Classifying normal-form meromorphic cusps from limits
-/

@[expose] public section

open Complex Metric Set Filter
open scoped Topology

namespace ThreeOmittedValues

theorem finite_fibre_of_punctured_limit {F : ℂ → ℂ} {x a : ℂ}
    (hF : MeromorphicNFAt F x) (hlim : Tendsto F (𝓝[≠] x) (𝓝 a)) :
    x ∈ finiteValueFiber F a := by
  have hord : 0 ≤ meromorphicOrderAt F x :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg hF.meromorphicAt).mp ⟨a, hlim⟩
  have ha := hF.meromorphicOrderAt_nonneg_iff_analyticAt.mp hord
  have hv : F x = a := tendsto_nhds_unique
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim
  exact ⟨ha, hv⟩

theorem one_fibre_of_normalized_limit {F : ℂ → ℂ} {x : ℂ}
    (hF : MeromorphicNFAt F x)
    (hlim : Tendsto (fun z => 1 - F z) (𝓝[≠] x) (𝓝 0)) :
    x ∈ finiteValueFiber F 1 := by
  have hlim' : Tendsto F (𝓝[≠] x) (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℂ))).sub hlim
    simpa [Function.comp_def] using h
  exact finite_fibre_of_punctured_limit hF hlim'

theorem pole_fibre_of_inverse_limit {F : ℂ → ℂ} {x : ℂ}
    (hF : MeromorphicNFAt F x)
    (hne : ∀ᶠ z in 𝓝[≠] x, F z ≠ 0)
    (hlim : Tendsto (fun z => (F z)⁻¹) (𝓝[≠] x) (𝓝 0)) :
    x ∈ poleFiber F := by
  have hne' : ∀ᶠ z in 𝓝[≠] x, (F z)⁻¹ ∈ ({0} : Set ℂ)ᶜ := by
    filter_upwards [hne] with z hz
    simpa using inv_ne_zero hz
  have hlim' : Tendsto (fun z => (F z)⁻¹) (𝓝[≠] x) (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, hne'⟩
  have hbig : Tendsto F (𝓝[≠] x) (Bornology.cobounded ℂ) := by
    have h := tendsto_inv₀_nhdsNE_zero.comp hlim'
    simpa [Function.comp_def] using h
  exact (mem_poleFiber_iff_order_lt_zero hF).mpr
    ((tendsto_cobounded_iff_meromorphicOrderAt_neg hF.meromorphicAt).mp hbig)

theorem infinite_fibre_of_injective_parameters (B : ℝ → ℂ) (Q : Set ℂ) (r : ℕ → ℂ)
    (hr : Function.Injective r)
    (hfamily : ∀ n : ℕ, ∃ x : ℝ, B x = r n ∧ (x : ℂ) ∈ Q) : Q.Infinite := by
  choose x hx using hfamily
  let p : ℕ → ℂ := fun n => (x n : ℂ)
  have hinj : Function.Injective p := by
    intro m n hmn
    have hxmn : x m = x n := Complex.ofReal_injective hmn
    apply hr
    calc
      r m = B (x m) := (hx m).1.symm
      _ = B (x n) := congrArg B hxmn
      _ = r n := (hx n).1
  apply (Set.infinite_range_of_injective hinj).mono
  rintro z ⟨n, rfl⟩
  exact (hx n).2

end ThreeOmittedValues
