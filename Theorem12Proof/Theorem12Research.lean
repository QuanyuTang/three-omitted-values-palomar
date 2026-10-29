module

public import Theorem12Proof.InteriorConstruction
public import Theorem12Proof.InteriorBoundedType
public import Theorem12Proof.BoundedTypeReflection
public import Theorem12Proof.FareySpecialFibres
public import Theorem12Proof.NonSummableDivisors
import Mathlib.Tactic

/-!
# Theorem 1.2: an unconditional formalization

The finite fibres require analyticity at the point because the complex-valued
normal form uses zero as the value at a pole. The divisor summands use the
positive part of the meromorphic divisor, hence count multiplicity.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set Filter NoWanderingDomains
open scoped MatrixGroups ModularForm Manifold Topology

namespace ThreeOmittedValues

def Theorem12Statement : Prop :=
  ∃ F : ℂ → ℂ,
    MeromorphicNFOn F Set.univ ∧
    (∀ z, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z)) ∧
    finiteValueFiber F 0 ⊆ {z : ℂ | z.im = 0} ∧
    finiteValueFiber F 1 ⊆ {z : ℂ | z.im = 0} ∧
    poleFiber F ⊆ {z : ℂ | z.im = 0} ∧
    (finiteValueFiber F 0).Infinite ∧
    (finiteValueFiber F 1).Infinite ∧
    (poleFiber F).Infinite ∧
    (∀ a : ℂ, a ≠ 0 → a ≠ 1 →
      ¬ upperBlaschkeCondition F a ∧ ¬ lowerBlaschkeCondition F a) ∧
    ¬ IsBoundedTypeOnUpper F ∧ ¬ IsBoundedTypeOnLower F

theorem theorem_1_2 : Theorem12Statement := by
  obtain ⟨levels, Φ, hlevels, _hbelow, _hvertices, _harcs, hupper, hΦ,
    _hΦinj, hΦimage, _hΦcenter, _hcomposite, _homit, hall, e, he, he1⟩ :=
    exists_farey_map_with_all_divergent_interior_fibres
  let F : ℂ → ℂ := fareyGlobalExtension e
  have hNF : MeromorphicNFOn F Set.univ := fareyGlobalExtension_normalForm e
  have hmer : MeromorphicOn F Set.univ := hNF.meromorphicOn
  have hsym : ∀ z, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z) :=
    fareyGlobalExtension_realSymmetric hupper hΦ hΦimage e he he1
  obtain ⟨h0real, h1real, hpreal, h0inf, h1inf, hpinf⟩ :=
    fareyGlobalExtension_exceptional_fibres hlevels hupper hΦ hΦimage e he he1
  obtain ⟨w, hw⟩ := h0inf.nonempty
  have hana : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im} := by
    intro z hz
    exact (fareyGlobalExtension_off_real hupper hΦ hΦimage e he he1 hz.ne').1
  have hallF : ∀ a : ℂ, a ≠ 0 → a ≠ 1 →
      ∃ (N : ℕ) (p : OrbitIndexFrom N → ℂ), Function.Injective p ∧
        (∀ i, 0 < (p i).im ∧ F (p i) = a) ∧
        ¬ Summable (fun i => blaschkeWeight (p i)) := by
    intro a ha0 ha1
    obtain ⟨N, p, hinj, hp, hdiv⟩ := hall a ha0 ha1
    refine ⟨N, p, hinj, ?_, hdiv⟩
    intro i
    exact ⟨(hp i).1, (fareyGlobalExtension_upper hupper hΦ hΦimage e he he1 (hp i).1).trans (hp i).2⟩
  have hdivisors : ∀ a : ℂ, a ≠ 0 → a ≠ 1 →
      ¬ upperBlaschkeCondition F a ∧ ¬ lowerBlaschkeCondition F a := by
    intro a ha0 ha1
    obtain ⟨N, p, hp_inj, hp, hp_div⟩ := hallF a ha0 ha1
    have hpfib (i : OrbitIndexFrom N) : p i ∈ finiteValueFiber F a :=
      ⟨hana (p i) (hp i).1, (hp i).2⟩
    have hu := not_upperBlaschke_of_nonsummable_points hmer hw (Ne.symm ha0) p hp_inj
      hpfib (fun i => (hp i).1) hp_div
    have hca0 : (starRingEnd ℂ) a ≠ 0 := by
      intro h
      apply ha0
      simpa using congrArg (starRingEnd ℂ) h
    have hca1 : (starRingEnd ℂ) a ≠ 1 := by
      intro h
      apply ha1
      simpa using congrArg (starRingEnd ℂ) h
    obtain ⟨M, q, hq_inj, hq, hq_div⟩ := hallF ((starRingEnd ℂ) a) hca0 hca1
    have hqfib (i : OrbitIndexFrom M) : q i ∈ finiteValueFiber F ((starRingEnd ℂ) a) :=
      ⟨hana (q i) (hq i).1, (hq i).2⟩
    have hl := not_lowerBlaschke_of_reflected_nonsummable_points hmer hw (Ne.symm ha0) hsym
      q hq_inj hqfib (fun i => (hq i).1) hq_div
    exact ⟨hu, hl⟩
  have hbu : ¬ IsBoundedTypeOnUpper F := not_boundedType_of_all_divergent_fibres hana hallF
  have hbl : ¬ IsBoundedTypeOnLower F := not_boundedType_lower_of_upper_of_realSymmetric hsym hbu
  exact ⟨F, hNF, hsym, h0real, h1real, hpreal, h0inf, h1inf, hpinf, hdivisors, hbu, hbl⟩

end ThreeOmittedValues
