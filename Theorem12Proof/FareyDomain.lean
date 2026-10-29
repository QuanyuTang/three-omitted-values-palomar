module

public import Theorem12Proof.FareyGraphIdentification
public import Theorem12Proof.FareyTranslated
public import Theorem12Proof.GraphTopology
public import Theorem12Proof.Vendor.DirichletRiemannMapping
import Mathlib.Tactic

/-!
# A simply connected Farey-boundary domain

This construction supplies a continuous proper graph made of determinant-one
semicircles below a prescribed positive continuous function, together with an
interior conformal disk map. Boundary extension, modular cusp continuation,
and the non-Blaschke conclusion remain separate obligations.
-/

@[expose] public section

open Set Metric

namespace ThreeOmittedValues

/-- Construct the Farey-edge graph below a positive continuous comparison
graph and obtain an interior Riemann map of the domain above it. -/
theorem exists_farey_domain_with_interior_map (β : ℝ → ℝ)
    (hβcont : Continuous β) (hβpos : ∀ x, 0 < β x) :
    ∃ (levels : ℤ → ℕ) (G : ℂ → ℂ),
      (∀ n, 1 ≤ levels n) ∧
      (∀ x, 0 ≤ pastedFareyHeight levels x ∧ pastedFareyHeight levels x < β x) ∧
      (∀ n : ℤ, pastedFareyHeight levels (n : ℝ) = 0 ∧
        pastedFareyHeight levels ((n : ℝ) + 1 / 2) = 0) ∧
      IsProperMap (graphMap (pastedFareyHeight levels)) ∧
      globalFareyArcs levels = Set.range (graphMap (pastedFareyHeight levels)) ∧
      IsOpen (upperGraphDomain (pastedFareyHeight levels)) ∧
      SimplyConnectedSpace (upperGraphDomain (pastedFareyHeight levels)) ∧
      upperGraphDomain β ⊆ upperGraphDomain (pastedFareyHeight levels) ∧
      upperGraphDomain (pastedFareyHeight levels) ⊆ {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ G (ball (0 : ℂ) 1) ∧ InjOn G (ball (0 : ℂ) 1) ∧
      G '' ball (0 : ℂ) 1 = upperGraphDomain (pastedFareyHeight levels) := by
  obtain ⟨levels, hlevels, hcont, hbelow⟩ :=
    exists_farey_height_below_positive β hβcont hβpos
  let h := pastedFareyHeight levels
  have hopen : IsOpen (upperGraphDomain h) := upperGraphDomain_isOpen hcont
  have hsc : SimplyConnectedSpace (upperGraphDomain h) := upperGraphDomain_simplyConnected hcont
  letI : SimplyConnectedSpace (upperGraphDomain h) := hsc
  have hnot : (0 : ℂ) ∉ upperGraphDomain h := by
    change ¬ h (0 : ℂ).re < (0 : ℂ).im
    simp only [Complex.zero_re, Complex.zero_im]
    exact not_lt_of_ge (hbelow 0).1
  have hne : upperGraphDomain h ≠ Set.univ := by
    intro heq
    apply hnot
    rw [heq]
    exact Set.mem_univ _
  obtain ⟨G, hG, hGinj, hGimage⟩ := riemann_mapping_theorem (upperGraphDomain h) hopen hne
  refine ⟨levels, G, hlevels, hbelow, ?_, graphMap_isProperMap hcont, ?_, hopen, hsc, ?_,
    upperGraphDomain_subset_upper (fun x => (hbelow x).1), hG, hGinj, hGimage⟩
  · intro n
    exact ⟨pastedFareyHeight_int levels n, pastedFareyHeight_half_int levels n (hlevels n)⟩
  · rw [globalFareyArcs_eq_graph, graphMap_range]
  · intro z hz
    exact (hbelow z.re).2.trans hz

end ThreeOmittedValues
