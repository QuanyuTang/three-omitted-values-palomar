module

public import Theorem12Proof.RequestProject.RiemannMappingCapWinding

/-!
# Boundary limits from a parametrized Jordan frontier

This derives the unique boundary-limit consequence of the Courant–Lebesgue
cap estimate using a supplied Lipschitz Jordan parametrization.  The proof
adapts `PolyaNeumann.riemannMapping_exists_unique_boundary_limit` from the
prior Apache-2.0 Neumann development, while omitting the stronger Lipschitz
domain assumption.  Applying it to the Farey boundary still requires an
actual proof of the stated parametrization hypotheses.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped Topology

namespace ThreeOmittedValues

/-- Every boundary point of the disk has a unique full interior limit under
a bounded univalent map whose frontier has the indicated parametrization. -/
theorem boundary_limit_of_lipschitz_jordan_frontier (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hγinj : InjOn γ (Ico 0 (2 * Real.pi)))
    (himage : γ '' Icc 0 (2 * Real.pi) = frontier (F '' ball (0 : ℂ) 1))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃! p : ℂ, p ∈ frontier (F '' ball (0 : ℂ) 1) ∧
      Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p) := by
  have hζcl : ζ ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0), mem_closedBall_zero_iff, hζ]
  letI : NeBot (𝓝[ball (0 : ℂ) 1] ζ) := mem_closure_iff_nhdsWithin_neBot.mp hζcl
  have hC : Cauchy (Filter.map F (𝓝[ball (0 : ℂ) 1] ζ)) := by
    apply Metric.cauchy_iff.mpr
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    obtain ⟨r, R, p, hr, _hrδ, _hr1, _hR, hRε, _hp, hcap⟩ :=
      PolyaNeumann.riemannMapping_exists_small_cap_region F hF hinj hb hK hper
        hγinj himage hζ (zero_lt_one : (0 : ℝ) < 1) (half_pos hε)
    have hmem : ball p R ∈ Filter.map F (𝓝[ball (0 : ℂ) 1] ζ) := by
      change F ⁻¹' ball p R ∈ 𝓝[ball (0 : ℂ) 1] ζ
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (ball_mem_nhds ζ hr)] with z hz hzcap
      exact hcap ⟨z, ⟨hz, hzcap⟩, rfl⟩
    refine ⟨ball p R, hmem, ?_⟩
    intro x hx y hy
    have hxp : dist x p < R := hx
    have hyp : dist y p < R := hy
    have hpy : dist p y < R := by simpa only [dist_comm] using hyp
    have ht := dist_triangle x p y
    linarith
  obtain ⟨p, hp⟩ := cauchy_map_iff_exists_tendsto.mp hC
  have hpf : p ∈ frontier (F '' ball (0 : ℂ) 1) :=
    PolyaNeumann.riemannMapping_limit_mem_frontier (l := 𝓝[ball (0 : ℂ) 1] ζ)
      (z := fun z : ℂ => z) F hF hinj hζ self_mem_nhdsWithin
      ((tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 ζ) (𝓝 ζ)).mono_left nhdsWithin_le_nhds) hp
  refine ⟨p, ⟨hpf, hp⟩, ?_⟩
  intro q hq
  exact tendsto_nhds_unique hq.2 hp

end ThreeOmittedValues
