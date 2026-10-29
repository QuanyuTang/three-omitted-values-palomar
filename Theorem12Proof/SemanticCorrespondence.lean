module

public import Theorem12Proof.Theorem12Research
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Correspondence with the source theorem's classical terminology

These proved bridges interpret finite and infinite fibres using `OnePoint`,
identify the actual multiplicity-weighted divisor sums, and compare the
bounded-type predicate with bounded holomorphic quotients on open domains.
The bounded-type equivalence assumes holomorphy on that domain; in the final
restatement it is derived from the already-proved real location of all poles.
This file does not introduce a separate Riemann-surface manifold formalism.
-/

@[expose] public section

open Set Filter
open scoped Topology OnePoint Classical

noncomputable section
namespace ThreeOmittedValues.SemanticCorrespondence
open ThreeOmittedValues

/-- Reading the normal-form representative as a function with a value at infinity. -/
def sphereValue (F : ℂ → ℂ) (z : ℂ) : OnePoint ℂ := by
  classical
  exact if AnalyticAt ℂ F z then (F z : OnePoint ℂ) else ∞

theorem sphere_finite_fiber (F : ℂ → ℂ) (a : ℂ) :
    sphereValue F ⁻¹' {(a : OnePoint ℂ)} = finiteValueFiber F a := by
  ext z
  by_cases h : AnalyticAt ℂ F z <;>
    simp [sphereValue, finiteValueFiber, h]

theorem sphere_pole_fiber (F : ℂ → ℂ) :
    sphereValue F ⁻¹' {(∞ : OnePoint ℂ)} = poleFiber F := by
  ext z
  by_cases h : AnalyticAt ℂ F z <;> simp [sphereValue, poleFiber, h]

theorem exceptional_values_iff (F : ℂ → ℂ) (z : ℂ) :
    sphereValue F z ∈ ({((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), ∞} : Set (OnePoint ℂ)) ↔
      z ∈ finiteValueFiber F 0 ∨ z ∈ finiteValueFiber F 1 ∨ z ∈ poleFiber F := by
  have h0 := Set.ext_iff.mp (sphere_finite_fiber F 0) z
  have h1 := Set.ext_iff.mp (sphere_finite_fiber F 1) z
  have hp := Set.ext_iff.mp (sphere_pole_fiber F) z
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff] using
    or_congr h0 (or_congr h1 hp)

theorem remaining_sphere_values (P : ℂ → Prop) :
    (∀ a : ℂ, a ≠ 0 → a ≠ 1 → P a) ↔
    (∀ a : OnePoint ℂ, a ≠ ((0 : ℂ) : OnePoint ℂ) →
      a ≠ ((1 : ℂ) : OnePoint ℂ) → a ≠ ∞ →
      ∃ b : ℂ, (b : OnePoint ℂ) = a ∧ P b) := by
  constructor
  · intro h a
    induction a using OnePoint.rec with
    | infty => simp
    | coe b =>
      intro hb0 hb1 _
      refine ⟨b, rfl, h b ?_ ?_⟩
      · exact fun hb => hb0 (congrArg OnePoint.some hb)
      · exact fun hb => hb1 (congrArg OnePoint.some hb)
  · intro h a ha0 ha1
    obtain ⟨b, hb, hP⟩ := h (a : OnePoint ℂ)
      (by simpa only [Ne, OnePoint.coe_eq_coe] using ha0)
      (by simpa only [Ne, OnePoint.coe_eq_coe] using ha1)
      (OnePoint.coe_ne_infty a)
    exact OnePoint.coe_injective hb ▸ hP

theorem multiplicity_positive_iff {F : ℂ → ℂ} {a b w z : ℂ}
    (hF : MeromorphicNFOn F Set.univ)
    (hw : w ∈ finiteValueFiber F b) (hba : b ≠ a) :
    0 < aPointMultiplicity F a z ↔ z ∈ finiteValueFiber F a := by
  constructor
  · intro hpos
    by_cases ha : AnalyticAt ℂ F z
    · refine ⟨ha, ?_⟩
      by_contra hne
      have hga : AnalyticAt ℂ (fun t => F t - a) z := ha.sub analyticAt_const
      have horder : meromorphicOrderAt (fun t => F t - a) z = 0 :=
        hga.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (sub_ne_zero.mpr hne)
      have hmer : MeromorphicOn (fun t => F t - a) Set.univ := by
        intro t ht
        exact (hF.meromorphicOn t ht).sub analyticAt_const.meromorphicAt
      have hzero : aPointMultiplicity F a z = 0 := by
        simp only [aPointMultiplicity, MeromorphicOn.divisor_apply hmer (Set.mem_univ z),
          horder, WithTop.untop₀_zero, Int.toNat_zero]
      omega
    · have hpole : meromorphicOrderAt F z < 0 :=
        (mem_poleFiber_iff_order_lt_zero (hF (Set.mem_univ z))).mp ha
      have hzero := aPointMultiplicity_eq_zero_at_pole (a := a) hF.meromorphicOn hpole
      omega
  · exact aPointMultiplicity_pos_of_distinct_value hF.meromorphicOn hw hba

theorem multiplicity_equals_analytic_zero_order {F : ℂ → ℂ} {a z : ℂ}
    (hF : MeromorphicOn F Set.univ) (hz : AnalyticAt ℂ F z) :
    aPointMultiplicity F a z = (analyticOrderAt (fun t => F t - a) z).toNat := by
  have hga : AnalyticAt ℂ (fun t => F t - a) z := hz.sub analyticAt_const
  have hmer : MeromorphicOn (fun t => F t - a) Set.univ := by
    intro t ht
    exact (hF t ht).sub analyticAt_const.meromorphicAt
  rw [aPointMultiplicity, MeromorphicOn.divisor_apply hmer (Set.mem_univ z),
    hga.meromorphicOrderAt_eq]
  generalize analyticOrderAt (fun t => F t - a) z = n
  induction n using ENat.recTopCoe <;> simp

theorem distinct_fibres_exclude_infinite_order {F : ℂ → ℂ}
    (hF : MeromorphicNFOn F Set.univ)
    (h0 : (finiteValueFiber F 0).Nonempty) (h1 : (finiteValueFiber F 1).Nonempty)
    (a z : ℂ) : meromorphicOrderAt (fun t => F t - a) z ≠ ⊤ := by
  by_cases ha : a = 0
  · obtain ⟨w, hw⟩ := h1
    exact aPoint_order_ne_top_of_distinct_value hF.meromorphicOn hw (by simp [ha])
  · obtain ⟨w, hw⟩ := h0
    exact aPoint_order_ne_top_of_distinct_value hF.meromorphicOn hw (Ne.symm ha)

/-- Summing over the plane with zero padding is exactly summing over the actual fibre. -/
theorem summable_on_actual_fiber {F : ℂ → ℂ} {a b w : ℂ}
    (hF : MeromorphicNFOn F Set.univ)
    (hw : w ∈ finiteValueFiber F b) (hba : b ≠ a) (U : Set ℂ) :
    Summable (fun z : ℂ => if z ∈ U then
      (aPointMultiplicity F a z : ℝ) * blaschkeWeight z else 0) ↔
    Summable (fun z : {z : ℂ | z ∈ U ∧ z ∈ finiteValueFiber F a} =>
      (aPointMultiplicity F a z : ℝ) * blaschkeWeight z) := by
  classical
  let S : Set ℂ := {z | z ∈ U ∧ z ∈ finiteValueFiber F a}
  let f : ℂ → ℝ := fun z => if z ∈ U then
    (aPointMultiplicity F a z : ℝ) * blaschkeWeight z else 0
  have hzero : ∀ z ∉ Set.range (Subtype.val : S → ℂ), f z = 0 := by
    intro z hz
    have hnotS : z ∉ S := by simpa only [Subtype.range_coe] using hz
    by_cases hzU : z ∈ U
    · have hnotF : z ∉ finiteValueFiber F a := fun hzF => hnotS ⟨hzU, hzF⟩
      have hm : aPointMultiplicity F a z = 0 := Nat.eq_zero_of_not_pos (fun hpos =>
        hnotF ((multiplicity_positive_iff hF hw hba).mp hpos))
      simp [f, hzU, hm]
    · simp [f, hzU]
  have h := (Subtype.val_injective : Function.Injective (Subtype.val : S → ℂ)).summable_iff hzero
  have hrestrict : f ∘ (Subtype.val : S → ℂ) =
      (fun z : S => (aPointMultiplicity F a z : ℝ) * blaschkeWeight z) := by
    funext z
    simp [f, z.property.1]
  rw [hrestrict] at h
  exact h.symm

theorem blaschke_terms_nonnegative (mult : ℂ → ℕ) (z : ℂ) :
    0 ≤ upperBlaschkeTerms mult z ∧ 0 ≤ lowerBlaschkeTerms mult z := by
  have hw : 0 ≤ blaschkeWeight z := div_nonneg (abs_nonneg _) (by positivity)
  constructor <;> simp only [upperBlaschkeTerms, lowerBlaschkeTerms] <;>
    split_ifs <;> positivity

/-- For these nonnegative terms, failure of summability means unbounded finite sums. -/
theorem not_summable_iff_unbounded_finite_sums {ι : Type*} (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (¬ Summable f) ↔ ∀ C : ℝ, ∃ s : Finset ι, C < ∑ i ∈ s, f i := by
  constructor
  · intro hn C
    by_contra h
    push Not at h
    exact hn (summable_of_sum_le hf h)
  · intro h hs
    obtain ⟨s, hlt⟩ := h (∑' i, f i)
    exact (not_lt_of_ge (hs.sum_le_tsum s (fun i _ => hf i))) hlt

/-- The usual holomorphic bounded quotient, with equality after multiplication. -/
def ClassicalBoundedTypeOn (F : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ u v : ℂ → ℂ,
    DifferentiableOn ℂ u U ∧ DifferentiableOn ℂ v U ∧
    Bornology.IsBounded (u '' U) ∧ Bornology.IsBounded (v '' U) ∧
    (∃ z ∈ U, v z ≠ 0) ∧ ∀ z ∈ U, F z * v z = u z

def BoundedQuotientOn (F : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ (u v : ℂ → ℂ) (Cu Cv : ℝ),
    AnalyticOnNhd ℂ u U ∧ AnalyticOnNhd ℂ v U ∧
    (∀ z ∈ U, ‖u z‖ ≤ Cu) ∧ (∀ z ∈ U, ‖v z‖ ≤ Cv) ∧
    (∃ z ∈ U, v z ≠ 0) ∧ ∀ z ∈ U, v z ≠ 0 → F z = u z / v z

theorem bounded_type_definitions_agree {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U) :
    BoundedQuotientOn F U ↔ ClassicalBoundedTypeOn F U := by
  constructor
  · rintro ⟨u, v, Cu, Cv, hu, hv, hub, hvb, hvnon, hratio⟩
    refine ⟨u, v, hu.differentiableOn, hv.differentiableOn, ?_, ?_, hvnon, ?_⟩
    · exact isBounded_iff_forall_norm_le.mpr ⟨Cu, by
        rintro _ ⟨z, hz, rfl⟩
        exact hub z hz⟩
    · exact isBounded_iff_forall_norm_le.mpr ⟨Cv, by
        rintro _ ⟨z, hz, rfl⟩
        exact hvb z hz⟩
    · let w : ℂ → ℂ := fun z => F z * v z - u z
      have hw : AnalyticOnNhd ℂ w U := fun z hz => ((hF z hz).mul (hv z hz)).sub (hu z hz)
      obtain ⟨p, hp, hvp⟩ := hvnon
      have hmem : v p ∈ ({0}ᶜ : Set ℂ) := hvp
      have hvnear : ∀ᶠ z in 𝓝 p, v z ≠ 0 :=
        (hv p hp).continuousAt.tendsto.eventually (isClosed_singleton.isOpen_compl.mem_nhds hmem)
      have hzero : w =ᶠ[𝓝 p] 0 := by
        filter_upwards [hU.mem_nhds hp, hvnear] with z hz hvz
        change F z * v z - u z = 0
        exact sub_eq_zero.mpr ((eq_div_iff hvz).mp (hratio z hz hvz))
      have hall := hw.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hp hzero
      intro z hz
      exact sub_eq_zero.mp (hall hz)
  · rintro ⟨u, v, hu, hv, hub, hvb, hvnon, heq⟩
    obtain ⟨Cu, hCu⟩ := isBounded_iff_forall_norm_le.mp hub
    obtain ⟨Cv, hCv⟩ := isBounded_iff_forall_norm_le.mp hvb
    refine ⟨u, v, Cu, Cv, hu.analyticOnNhd hU, hv.analyticOnNhd hU, ?_, ?_, hvnon, ?_⟩
    · exact fun z hz => hCu (u z) ⟨z, hz, rfl⟩
    · exact fun z hz => hCv (v z) ⟨z, hz, rfl⟩
    · exact fun z hz hvz => (eq_div_iff hvz).mpr (heq z hz)

theorem bounded_type_upper_agrees {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im}) :
    IsBoundedTypeOnUpper F ↔ ClassicalBoundedTypeOn F {z : ℂ | 0 < z.im} :=
  bounded_type_definitions_agree (isOpen_lt continuous_const Complex.continuous_im)
    (convex_halfSpace_im_gt 0).isPreconnected hF

theorem bounded_type_lower_agrees {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | z.im < 0}) :
    IsBoundedTypeOnLower F ↔ ClassicalBoundedTypeOn F {z : ℂ | z.im < 0} :=
  bounded_type_definitions_agree (isOpen_lt Complex.continuous_im continuous_const)
    (convex_halfSpace_im_lt 0).isPreconnected hF

theorem analytic_off_real_of_real_poles {F : ℂ → ℂ}
    (hp : poleFiber F ⊆ {z : ℂ | z.im = 0}) {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ F z := by
  by_contra h
  exact hz (hp h)

/-- All clauses of the source theorem, with sphere-valued fibres, sums on
the actual point divisors, and the ordinary bounded-holomorphic quotient. -/
theorem source_form_with_semantic_bridges :
    ∃ F : ℂ → ℂ,
      MeromorphicNFOn F Set.univ ∧
      (∀ z, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z)) ∧
      (sphereValue F ⁻¹' ({((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), ∞} : Set (OnePoint ℂ))) ⊆
        {z : ℂ | z.im = 0} ∧
      (sphereValue F ⁻¹' {((0 : ℂ) : OnePoint ℂ)}).Infinite ∧
      (sphereValue F ⁻¹' {((1 : ℂ) : OnePoint ℂ)}).Infinite ∧
      (sphereValue F ⁻¹' {(∞ : OnePoint ℂ)}).Infinite ∧
      (∀ a : ℂ, a ≠ 0 → a ≠ 1 →
        (¬ Summable (fun z : {z : ℂ | 0 < z.im ∧ z ∈ finiteValueFiber F a} =>
          (aPointMultiplicity F a z : ℝ) * blaschkeWeight z)) ∧
        (¬ Summable (fun z : {z : ℂ | z.im < 0 ∧ z ∈ finiteValueFiber F a} =>
          (aPointMultiplicity F a z : ℝ) * blaschkeWeight z))) ∧
      ¬ ClassicalBoundedTypeOn F {z : ℂ | 0 < z.im} ∧
      ¬ ClassicalBoundedTypeOn F {z : ℂ | z.im < 0} := by
  obtain ⟨F, hNF, hsym, h0real, h1real, hpreal, h0inf, h1inf, hpinf, hdiv, hbu, hbl⟩ :=
    ThreeOmittedValues.theorem_1_2
  have hupper : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im} :=
    fun z hz => analytic_off_real_of_real_poles hpreal hz.ne'
  have hlower : AnalyticOnNhd ℂ F {z : ℂ | z.im < 0} :=
    fun z hz => analytic_off_real_of_real_poles hpreal hz.ne
  refine ⟨F, hNF, hsym, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (exceptional_values_iff F z).mp hz with h0 | h1 | hp
    · exact h0real h0
    · exact h1real h1
    · exact hpreal hp
  · simpa only [sphere_finite_fiber] using h0inf
  · simpa only [sphere_finite_fiber] using h1inf
  · simpa only [sphere_pole_fiber] using hpinf
  · intro a ha0 ha1
    obtain ⟨w, hw⟩ := h0inf.nonempty
    exact ⟨(not_congr (summable_on_actual_fiber hNF hw (Ne.symm ha0)
      {z : ℂ | 0 < z.im})).mp (hdiv a ha0 ha1).1,
      (not_congr (summable_on_actual_fiber hNF hw (Ne.symm ha0)
      {z : ℂ | z.im < 0})).mp (hdiv a ha0 ha1).2⟩
  · exact fun h => hbu ((bounded_type_upper_agrees hupper).mpr h)
  · exact fun h => hbl ((bounded_type_lower_agrees hlower).mpr h)


end ThreeOmittedValues.SemanticCorrespondence
