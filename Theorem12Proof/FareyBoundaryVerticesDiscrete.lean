module

public import Theorem12Proof.FareyVertexLocalFinite
public import Theorem12Proof.FareyBoundaryValues
import Mathlib.Tactic

/-!
# The real preimages of Farey vertices are isolated

The boundary correspondence is continuous and injective. Its image of the
real axis lies on the Farey graph, whose vertices form a locally finite set.
-/

@[expose] public section

open Complex Metric Set Filter NoWanderingDomains
open scoped Topology

namespace ThreeOmittedValues

theorem halfPlaneExtension_real_continuous {Ω : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ closure (halfPlaneToCayley '' Ω))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) :
    Continuous (fun x : ℝ => halfPlaneContinuousExtension e (x : ℂ)) := by
  have hinto : Continuous (fun x : ℝ => (⟨(x : ℂ), by simp⟩ : {z : ℂ // 0 ≤ z.im})) :=
    Complex.continuous_ofReal.subtype_mk _
  have h := (closedHalfPlaneMap_continuous e he1).comp hinto
  simpa [halfPlaneContinuousExtension, Function.comp_def] using! h

theorem halfPlaneExtension_real_injective {Ω : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ closure (halfPlaneToCayley '' Ω))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) :
    Function.Injective (fun x : ℝ => halfPlaneContinuousExtension e (x : ℂ)) := by
  intro x y hxy
  let zx : {z : ℂ // 0 ≤ z.im} := ⟨(x : ℂ), by simp⟩
  let zy : {z : ℂ // 0 ≤ z.im} := ⟨(y : ℂ), by simp⟩
  let qx := closedHalfPlaneCayley zx
  let qy := closedHalfPlaneCayley zy
  have hCayley := congrArg halfPlaneToCayley hxy
  have hxf : halfPlaneContinuousExtension e (x : ℂ) = cayleyToHalfPlane (e qx) := by
    simp [halfPlaneContinuousExtension, closedHalfPlaneMap, qx, zx]
  have hyf : halfPlaneContinuousExtension e (y : ℂ) = cayleyToHalfPlane (e qy) := by
    simp [halfPlaneContinuousExtension, closedHalfPlaneMap, qy, zy]
  change halfPlaneToCayley (halfPlaneContinuousExtension e (x : ℂ)) =
    halfPlaneToCayley (halfPlaneContinuousExtension e (y : ℂ)) at hCayley
  rw [hxf, hyf] at hCayley
  rw [halfPlaneToCayley_cayleyToHalfPlane_of_ne_one (closedDiskBoundaryImage_ne_one e he1 zx),
    halfPlaneToCayley_cayleyToHalfPlane_of_ne_one (closedDiskBoundaryImage_ne_one e he1 zy)] at hCayley
  have heq : e qx = e qy := Subtype.ext hCayley
  have hC := congrArg Subtype.val (e.injective heq)
  have hdenx : (x : ℂ) + Complex.I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  have hdeny : (y : ℂ) + Complex.I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  exact Complex.ofReal_injective (halfPlaneToCayley_injective_of_denominators hdenx hdeny hC)

theorem farey_preimage_vertices_locally_finite {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      (ball x r ∩ {y : ℝ | (halfPlaneContinuousExtension e (y : ℂ)).im = 0}).Finite := by
  let B : ℝ → ℂ := fun y => halfPlaneContinuousExtension e (y : ℂ)
  let h := pastedFareyHeight levels
  let t := (B x).re
  have hB : Continuous B := halfPlaneExtension_real_continuous e he1
  have hBinj : Function.Injective B := halfPlaneExtension_real_injective e he1
  have hre : Continuous (fun y : ℝ => (B y).re) := Complex.continuous_re.comp hB
  have hnear : {y : ℝ | (B y).re ∈ ball t 1} ∈ 𝓝 x :=
    hre.continuousAt.tendsto (ball_mem_nhds _ (by norm_num))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  let V : Set ℝ := ball t 1 ∩ {u : ℝ | h u = 0}
  let W : Set ℂ := graphMap h '' V
  have hVfin : V.Finite := pastedFarey_zeros_locally_finite levels t
  have hWfin : W.Finite := hVfin.image (graphMap h)
  refine ⟨r, hr, (hWfin.preimage hBinj.injOn).subset ?_⟩
  intro y hy
  have hynear : (B y).re ∈ ball t 1 := hrsub hy.1
  obtain ⟨u, hu⟩ := halfPlaneContinuousExtension_boundary hΦimage e he he1 (z := (y : ℂ)) (by simp)
  have hu0 : h u = 0 := by
    have hi := hy.2
    change (halfPlaneContinuousExtension e (y : ℂ)).im = 0 at hi
    rw [hu] at hi
    simpa [graphMap] using hi
  have hut : u ∈ ball t 1 := by
    change (halfPlaneContinuousExtension e (y : ℂ)).re ∈ ball t 1 at hynear
    rw [hu] at hynear
    simpa [graphMap] using hynear
  exact ⟨u, ⟨hut, hu0⟩, hu.symm⟩

theorem farey_preimage_vertex_isolated {levels : ℤ → ℕ} {Φ : ℂ → ℂ}
    (hΦimage : Φ '' {z : ℂ | 0 < z.im} = upperGraphDomain (pastedFareyHeight levels))
    (e : closedBall (0 : ℂ) 1 ≃ₜ
      closure (halfPlaneToCayley '' upperGraphDomain (pastedFareyHeight levels)))
    (he : ∀ z : closedBall (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) 1 →
      (e z : ℂ) = halfPlaneToCayley (Φ (cayleyToHalfPlane z)))
    (he1 : (e ⟨1, by simp⟩ : ℂ) = 1) (x : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x r,
      (halfPlaneContinuousExtension e (y : ℂ)).im = 0 → y = x := by
  obtain ⟨r, hr, hfinite⟩ := farey_preimage_vertices_locally_finite hΦimage e he he1 x
  let V : Set ℝ := ball x r ∩ {y : ℝ | (halfPlaneContinuousExtension e (y : ℂ)).im = 0}
  have hclosed : IsClosed (V \ {x}) := (hfinite.subset sdiff_subset).isClosed
  have hx : x ∈ (V \ {x})ᶜ := by simp
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl x hx
  refine ⟨min r ε, lt_min hr hε, ?_⟩
  intro y hy hyzero
  have hyr : y ∈ ball x r := by
    exact (ball_subset_ball (min_le_left _ _)) hy
  have hyε : y ∈ ball x ε := by
    exact (ball_subset_ball (min_le_right _ _)) hy
  have hynot := hεsub hyε
  by_contra hne
  exact hynot ⟨⟨hyr, hyzero⟩, by simpa using hne⟩

end ThreeOmittedValues
