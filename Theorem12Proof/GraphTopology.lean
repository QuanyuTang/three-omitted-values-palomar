module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic

/-!
# Topology of a continuous graph

This module proves general topological properties needed for the Farey
boundary and comparison domains. It makes no claim that a conformal map
extends injectively to the boundary.
-/

@[expose] public section

open Set

namespace ThreeOmittedValues

noncomputable section

def graphMap (h : ℝ → ℝ) (x : ℝ) : ℂ := (x : ℂ) + (h x : ℂ) * Complex.I

@[simp] theorem graphMap_re (h : ℝ → ℝ) (x : ℝ) : (graphMap h x).re = x := by
  simp [graphMap]

@[simp] theorem graphMap_im (h : ℝ → ℝ) (x : ℝ) : (graphMap h x).im = h x := by
  simp [graphMap]

theorem graphMap_continuous {h : ℝ → ℝ} (hh : Continuous h) : Continuous (graphMap h) := by
  unfold graphMap
  fun_prop

theorem graphMap_range (h : ℝ → ℝ) :
    Set.range (graphMap h) = {z : ℂ | z.im = h z.re} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro hz
    change z.im = h z.re at hz
    refine ⟨z.re, ?_⟩
    apply Complex.ext
    · simp
    · simpa using hz.symm

/-- A continuous real graph is a closed embedding, hence a proper map. -/
theorem graphMap_isClosedEmbedding {h : ℝ → ℝ} (hh : Continuous h) :
    Topology.IsClosedEmbedding (graphMap h) := by
  have hleft : Function.LeftInverse Complex.re (graphMap h) := by
    intro x
    exact graphMap_re h x
  have he := hleft.isEmbedding Complex.continuous_re (graphMap_continuous hh)
  refine ⟨he, ?_⟩
  rw [graphMap_range]
  exact isClosed_eq Complex.continuous_im (hh.comp Complex.continuous_re)

theorem graphMap_isProperMap {h : ℝ → ℝ} (hh : Continuous h) : IsProperMap (graphMap h) :=
  (graphMap_isClosedEmbedding hh).isProperMap

def upperGraphDomain (h : ℝ → ℝ) : Set ℂ := {z | h z.re < z.im}

theorem upperGraphDomain_isOpen {h : ℝ → ℝ} (hh : Continuous h) :
    IsOpen (upperGraphDomain h) :=
  isOpen_lt (hh.comp Complex.continuous_re) Complex.continuous_im

theorem upperGraphDomain_subset_upper {h : ℝ → ℝ} (h0 : ∀ x, 0 ≤ h x) :
    upperGraphDomain h ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (h0 z.re).trans_lt hz

/-- Vertical shearing sends the domain above a continuous graph to the
upper half-plane. -/
def graphShear (h : ℝ → ℝ) (hh : Continuous h) : ℂ ≃ₜ ℂ where
  toFun z := z - (h z.re : ℂ) * Complex.I
  invFun z := z + (h z.re : ℂ) * Complex.I
  left_inv z := by apply Complex.ext <;> simp
  right_inv z := by apply Complex.ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem graphShear_image_upperGraphDomain {h : ℝ → ℝ} (hh : Continuous h) :
    graphShear h hh '' upperGraphDomain h = {z : ℂ | 0 < z.im} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change 0 < (w - (h w.re : ℂ) * Complex.I).im
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero]
    exact sub_pos.mpr hw
  · intro hz
    change 0 < z.im at hz
    refine ⟨(graphShear h hh).symm z, ?_, (graphShear h hh).apply_symm_apply z⟩
    change h (z + (h z.re : ℂ) * Complex.I).re < (z + (h z.re : ℂ) * Complex.I).im
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, mul_one]
    linarith

/-- The domain above any continuous graph is simply connected. -/
theorem upperGraphDomain_simplyConnected {h : ℝ → ℝ} (hh : Continuous h) :
    SimplyConnectedSpace (upperGraphDomain h) := by
  let U : Set ℂ := {z | 0 < z.im}
  have hU : Convex ℝ U := convex_halfSpace_im_gt 0
  haveI : ContractibleSpace U := hU.contractibleSpace ⟨Complex.I, by simp [U]⟩
  haveI : SimplyConnectedSpace U := inferInstance
  let e := (graphShear h hh).isEmbedding.homeomorphImage (upperGraphDomain h)
  have himage : graphShear h hh '' upperGraphDomain h = U := graphShear_image_upperGraphDomain hh
  exact (e.trans (Homeomorph.setCongr himage)).toHomotopyEquiv.simplyConnectedSpace

end

end ThreeOmittedValues
