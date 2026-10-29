module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Operator.Compact
public import Mathlib.Tactic

/-!
# Definitions (Section 1 of the paper)

We identify `ℝ²` with `ℂ`, as in the paper.

* `PolyaNeumann.IsDomain`, `PolyaNeumann.IsLipschitzDomain` : (Lipschitz) domains.
* `PolyaNeumann.TestFunction` : `C_c^∞(Ω)` test functions.
* `PolyaNeumann.IsWeakGradient` : weak first derivatives in `L²(Ω)`; an element of
  `L²(Ω)` with a weak gradient is exactly an element of `H¹(Ω)`.
* `PolyaNeumann.neumannEnergy` : the Neumann form `q_Ω[u,u] = ∫_Ω |∇u|²` (equal to `⊤`
  outside `H¹(Ω)`).
* `PolyaNeumann.neumannEigenvalue` : the Neumann eigenvalues `μ_j(Ω)`, defined via the
  min–max (Courant–Fischer) formula of Lemma 3.3 of the paper.
* `PolyaNeumann.neumannCount` : the strict counting function `N_N(E)`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace PolyaNeumann

/-- A domain: a nonempty connected open subset of `ℝ² = ℂ`. -/
def IsDomain (Ω : Set ℂ) : Prop := IsOpen Ω ∧ IsConnected Ω

/-- A Lipschitz domain: a domain whose boundary is locally, after a rigid change of
coordinates `w ↦ c * (w - p)` (`‖c‖ = 1`), the graph of a Lipschitz function `f`, with the
domain lying on one side (above the graph). -/
def IsLipschitzDomain (Ω : Set ℂ) : Prop :=
  IsDomain Ω ∧
  ∀ p ∈ frontier Ω, ∃ (c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ),
    ‖c‖ = 1 ∧ 0 < r ∧ 0 < h ∧ LipschitzWith K f ∧ f 0 = 0 ∧
    (∀ x : ℝ, |x| < r → |f x| < h) ∧
    ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im)

/-- `L²(Ω)` (complex valued, with respect to two-dimensional Lebesgue measure on `Ω`). -/
abbrev L2 (Ω : Set ℂ) := Lp ℂ 2 (volume.restrict Ω)

/-- The coordinate directions `e_x = 1`, `e_y = i` of `ℝ² = ℂ`. -/
def coordDir : Fin 2 → ℂ := ![1, Complex.I]

/-- Smooth compactly supported test functions on `Ω` (`C_c^∞(Ω)`). -/
def TestFunction (Ω : Set ℂ) (φ : ℂ → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- `g` is the weak gradient of `u` on `Ω`: `∫_Ω u ∂_i φ = - ∫_Ω g_i φ` for every
test function `φ` and `i ∈ {x, y}`. -/
def IsWeakGradient (Ω : Set ℂ) (u : L2 Ω) (g : Fin 2 → L2 Ω) : Prop :=
  ∀ φ : ℂ → ℂ, TestFunction Ω φ → ∀ i : Fin 2,
    ∫ w in Ω, u w * fderiv ℝ φ w (coordDir i) = - ∫ w in Ω, g i w * φ w

/-- The Sobolev space `H¹(Ω)`, as a subset of `L²(Ω)`. -/
def H1 (Ω : Set ℂ) : Set (L2 Ω) := {u | ∃ g, IsWeakGradient Ω u g}

/-- The Neumann form `q_Ω[u,u] = ∫_Ω |∇u|²`, with value `⊤` if `u ∉ H¹(Ω)`. -/
def neumannEnergy (Ω : Set ℂ) (u : L2 Ω) : ENNReal :=
  ⨅ (g : Fin 2 → L2 Ω) (_ : IsWeakGradient Ω u g), ∑ i, (‖g i‖₊ : ENNReal) ^ 2

/-- The Rayleigh quotient `q_Ω[u,u] / ‖u‖²`. -/
def rayleigh (Ω : Set ℂ) (u : L2 Ω) : ENNReal :=
  neumannEnergy Ω u / (‖u‖₊ : ENNReal) ^ 2

/-- The Neumann eigenvalues `μ_j(Ω)`, `j ≥ 0`, counted with multiplicity, given by the
min–max formula
`μ_j = inf_{S ⊂ H¹, dim S = j+1} sup_{0 ≠ u ∈ S} q_Ω[u,u] / ‖u‖²`.
(Subspaces not contained in `H¹(Ω)` have supremum `⊤` and so do not contribute.) -/
def neumannEigenvalue (Ω : Set ℂ) (j : ℕ) : ENNReal :=
  ⨅ (S : Submodule ℂ (L2 Ω)) (_ : Module.finrank ℂ S = j + 1),
    ⨆ (u : L2 Ω) (_ : u ∈ S) (_ : u ≠ 0), rayleigh Ω u

/-- The strict counting function `N_N(E) = #{j ∈ ℕ₀ : μ_j(Ω) < E}`. -/
def neumannCount (Ω : Set ℂ) (E : ENNReal) : ℕ∞ :=
  {j : ℕ | neumannEigenvalue Ω j < E}.encard

end PolyaNeumann

end
