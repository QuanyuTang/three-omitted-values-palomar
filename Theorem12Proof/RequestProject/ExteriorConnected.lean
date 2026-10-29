module

public import Theorem12Proof.RequestProject.JordanWinding

/-!
# Connectedness of the exterior of a Lipschitz domain with connected boundary

If `Ω` is a bounded Lipschitz domain whose boundary `∂Ω` is (pre)connected, then the exterior
`ℂ \ Ω̄` is connected (`isConnected_compl_closure_of_frontier`). The proof is local: below the
graph, every Lipschitz chart box contains a connected piece of the exterior that accumulates
at every boundary point of the box, and the boundary points adjacent to a given exterior
component form a relatively clopen subset of `∂Ω`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- Approach along a fixed direction. -/
lemma tendsto_add_mul_nhdsGT (w d : ℂ) :
    Tendsto (fun t : ℝ => w + (t : ℂ) * d) (𝓝[>] 0) (𝓝 w) := by
  have hc : Continuous (fun t : ℝ => w + (t : ℂ) * d) := by fun_prop
  exact tendsto_nhdsWithin_of_tendsto_nhds (hc.tendsto' 0 w (by simp))

/-- The exterior piece of a Lipschitz chart box. For a boundary point `q` of a Lipschitz
domain there are an open neighbourhood `V` of `q` and a preconnected set `B` in the exterior
`ℂ \ Ω̄` such that every exterior point of `V` lies in `B`, and every boundary point in `V` is
in the closure of `B`. -/
lemma exists_exterior_box {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) {q : ℂ}
    (hq : q ∈ frontier Ω) :
    ∃ V B : Set ℂ, IsOpen V ∧ q ∈ V ∧ IsPreconnected B ∧ B ⊆ (closure Ω)ᶜ ∧
      V ∩ (closure Ω)ᶜ ⊆ B ∧ ∀ q' ∈ frontier Ω ∩ V, q' ∈ closure B := by
  obtain ⟨c, r, h, K, f, hc, hr, hh, hf, -, hfb, hΩ⟩ := hL.2 q hq
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hc; exact zero_ne_one hc
  set g : ℂ → ℂ := fun w => c * (w - q) with hg
  have hgc : Continuous g := by fun_prop
  have hginv : ∀ u : ℂ, g (q + c⁻¹ * u) = u := fun u => by
    simp only [hg]; field_simp; ring
  have hgadd : ∀ (w : ℂ) (t : ℝ) (e : ℂ), g (w + t * (c⁻¹ * e)) = g w + t * e := fun w t e => by
    simp only [hg]; field_simp; ring
  set V : Set ℂ := {w | |(g w).re| < r ∧ |(g w).im| < h} with hV
  set B : Set ℂ := {w | (|(g w).re| < r ∧ |(g w).im| < h) ∧ (g w).im < f (g w).re} with hB
  refine ⟨V, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isOpen_lt (Complex.continuous_re.comp hgc).abs continuous_const).inter
      (isOpen_lt (Complex.continuous_im.comp hgc).abs continuous_const)
  · simp [hV, hg, hr, hh]
  · set Φ : ℝ × ℝ → ℂ := fun p =>
      q + c⁻¹ * ((p.1 : ℂ) + ((-h + p.2 * (f p.1 + h) : ℝ) : ℂ) * Complex.I) with hΦ
    have hBΦ : B = Φ '' (Ioo (-r) r ×ˢ Ioo 0 1) := by
      ext w
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have hfx : -h < f (g w).re := (abs_lt.mp (hfb _ h1)).1
        have hy : -h < (g w).im := (abs_lt.mp h2).1
        refine ⟨((g w).re, ((g w).im + h) / (f (g w).re + h)),
          ⟨abs_lt.mp h1, div_pos (by linarith) (by linarith),
            (div_lt_one (by linarith)).mpr (by linarith)⟩, ?_⟩
        have h4 : -h + ((g w).im + h) / (f (g w).re + h) * (f (g w).re + h) = (g w).im := by
          rw [div_mul_cancel₀ _ (show f (g w).re + h ≠ 0 by linarith)]
          ring
        simp only [hΦ, h4, Complex.re_add_im]
        simp only [hg]
        field_simp
        ring
      · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
        have hfx : -h < f x := (abs_lt.mp (hfb x (abs_lt.mpr hx))).1
        have hfx' : f x < h := (abs_lt.mp (hfb x (abs_lt.mpr hx))).2
        have hgΦ : g (Φ (x, t)) = (x : ℂ) + ((-h + t * (f x + h) : ℝ) : ℂ) * Complex.I :=
          hginv _
        have hre : (g (Φ (x, t))).re = x := by rw [hgΦ]; simp
        have him : (g (Φ (x, t))).im = -h + t * (f x + h) := by rw [hgΦ]; simp
        have h5 : t * (f x + h) < f x + h := by nlinarith [ht.1, ht.2]
        have h6 : 0 < t * (f x + h) := mul_pos ht.1 (by linarith)
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hre]; exact abs_lt.mpr hx
        · rw [him]; exact abs_lt.mpr ⟨by linarith, by linarith⟩
        · rw [hre, him]; linarith
    rw [hBΦ]
    refine (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ (Continuous.continuousOn ?_)
    have := hf.continuous
    fun_prop
  · rintro w ⟨⟨h1, h2⟩, h3⟩
    exact chart_notMem_closure hf hΩ h1 h2 h3
  · rintro w ⟨⟨h1, h2⟩, hwE⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    have hle : (g w).im ≤ f (g w).re :=
      not_lt.mp fun hlt => hwE (subset_closure ((hΩ w h1 h2).mpr hlt))
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hwE
      refine mem_closure_of_tendsto (tendsto_add_mul_nhdsGT w (c⁻¹ * Complex.I)) ?_
      filter_upwards [Ioo_mem_nhdsGT (show 0 < h - (g w).im by linarith [(abs_lt.mp h2).2])]
        with t ht
      have hre : (g (w + t * (c⁻¹ * Complex.I))).re = (g w).re := by rw [hgadd]; simp
      have him : (g (w + t * (c⁻¹ * Complex.I))).im = (g w).im + t := by rw [hgadd]; simp
      rw [hΩ _ (by rw [hre]; exact h1)
        (by rw [him]; exact abs_lt.mpr ⟨by linarith [(abs_lt.mp h2).1, ht.1], by linarith [ht.2]⟩),
        hre, him]
      linarith [ht.1]
  · rintro q' ⟨hq', h1, h2⟩
    have hgraph := chart_frontier_graph hL.1.1 hf hΩ hq' h1 h2
    have hfx : -h < f (g q').re := (abs_lt.mp (hfb _ h1)).1
    have hfx' : f (g q').re < h := (abs_lt.mp (hfb _ h1)).2
    refine mem_closure_of_tendsto (tendsto_add_mul_nhdsGT q' (c⁻¹ * -Complex.I)) ?_
    filter_upwards [Ioo_mem_nhdsGT (show 0 < f (g q').re + h by linarith)] with t ht
    have hre : (g (q' + t * (c⁻¹ * -Complex.I))).re = (g q').re := by rw [hgadd]; simp
    have him : (g (q' + t * (c⁻¹ * -Complex.I))).im = (g q').im - t := by
      rw [hgadd]; simp; ring
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hre]; exact h1
    · rw [him, hgraph]; exact abs_lt.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · rw [hre, him, hgraph]; linarith [ht.1]

/-- Every exterior component of a bounded domain accumulates at a boundary point. -/
lemma exists_frontier_mem_closure_connectedComponentIn {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hne : Ω.Nonempty) {x : ℂ} (hx : x ∈ (closure Ω)ᶜ) :
    ∃ q ∈ frontier Ω, q ∈ closure (connectedComponentIn (closure Ω)ᶜ x) := by
  set E := (closure Ω)ᶜ with hE
  have hEo : IsOpen E := isClosed_closure.isOpen_compl
  set C := connectedComponentIn E x with hC
  have hCo : IsOpen C := hEo.connectedComponentIn
  have hxC : x ∈ C := mem_connectedComponentIn hx
  obtain ⟨z₀, hz₀⟩ := hne
  have hCne : C ≠ univ := fun h => by
    have hz : z₀ ∈ C := by rw [h]; exact mem_univ z₀
    exact (connectedComponentIn_subset E x hz) (subset_closure hz₀)
  obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr ⟨⟨x, hxC⟩, hCne⟩
  have hzcl : z ∈ closure C := frontier_subset_closure hz
  have hzC : z ∉ C := by rw [hCo.frontier_eq] at hz; exact hz.2
  have hzE : z ∉ E := by
    intro hzE
    have hzo : IsOpen (connectedComponentIn E z) := hEo.connectedComponentIn
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hzcl _ hzo (mem_connectedComponentIn hzE)
    have h1 : connectedComponentIn E z = connectedComponentIn E w := connectedComponentIn_eq hw1
    have h2 : C = connectedComponentIn E w := connectedComponentIn_eq hw2
    exact hzC (h2 ▸ h1 ▸ mem_connectedComponentIn hzE)
  have hzΩ : z ∉ Ω := by
    intro hzΩ
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hzcl _ hΩo hzΩ
    exact connectedComponentIn_subset E x hw2 (subset_closure hw1)
  refine ⟨z, ?_, hzcl⟩
  rw [hΩo.frontier_eq]
  exact ⟨by simpa [hE] using hzE, hzΩ⟩

/-- **Exterior connectedness.** A bounded Lipschitz domain with preconnected boundary has
connected exterior `ℂ \ Ω̄`. -/
theorem isConnected_compl_closure_of_frontier {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hfc : IsPreconnected (frontier Ω)) :
    IsConnected (closure Ω)ᶜ := by
  set E := (closure Ω)ᶜ with hE
  have hΩo : IsOpen Ω := hL.1.1
  have hne : Ω.Nonempty := hL.1.2.nonempty
  choose! V B hVo hqV hBpre hBE hVB hcl using
    fun q (hq : q ∈ frontier Ω) => exists_exterior_box hL hq
  -- a box meeting the closure of an exterior component has its exterior piece inside it
  have hK : ∀ x ∈ E, ∀ q ∈ frontier Ω, ∀ w ∈ V q, w ∈ closure (connectedComponentIn E x) →
      B q ⊆ connectedComponentIn E x := by
    intro x hx q hq w hwV hwcl
    obtain ⟨v, hv1, hv2⟩ := mem_closure_iff.mp hwcl _ (hVo q hq) hwV
    have hvE : v ∈ E := connectedComponentIn_subset E x hv2
    have hvB : v ∈ B q := hVB q hq ⟨hv1, hvE⟩
    rw [connectedComponentIn_eq hv2]
    exact (hBpre q hq).subset_connectedComponentIn hvB (hBE q hq)
  have hiff : ∀ x ∈ E, ∀ q ∈ frontier Ω, ∀ q' ∈ frontier Ω ∩ V q,
      (q ∈ closure (connectedComponentIn E x) ↔ q' ∈ closure (connectedComponentIn E x)) := by
    intro x hx q hq q' hq'
    constructor
    · intro h
      exact closure_mono (hK x hx q hq q (hqV q hq) h) (hcl q hq q' hq')
    · intro h
      exact closure_mono (hK x hx q hq q' hq'.2 h) (hcl q hq q ⟨hq, hqV q hq⟩)
  -- every boundary point is adjacent to every exterior component
  have hall : ∀ x ∈ E, frontier Ω ⊆ closure (connectedComponentIn E x) := by
    intro x hx
    set C := connectedComponentIn E x with hC
    set u : Set ℂ := ⋃ q ∈ frontier Ω ∩ closure C, V q with hu
    set v : Set ℂ := ⋃ q ∈ frontier Ω \ closure C, V q with hv
    have huo : IsOpen u := isOpen_biUnion fun q hq => hVo q hq.1
    have hvo : IsOpen v := isOpen_biUnion fun q hq => hVo q hq.1
    have hcov : frontier Ω ⊆ u ∪ v := by
      intro q hq
      by_cases h : q ∈ closure C
      · exact Or.inl (mem_biUnion ⟨hq, h⟩ (hqV q hq))
      · exact Or.inr (mem_biUnion ⟨hq, h⟩ (hqV q hq))
    have hdisj : frontier Ω ∩ (u ∩ v) = ∅ := by
      ext p
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hp hpu hpv
      obtain ⟨q₁, hq₁, hp₁⟩ := mem_iUnion₂.mp hpu
      obtain ⟨q₂, hq₂, hp₂⟩ := mem_iUnion₂.mp hpv
      have h1 : p ∈ closure C := (hiff x hx q₁ hq₁.1 p ⟨hp, hp₁⟩).mp hq₁.2
      exact hq₂.2 ((hiff x hx q₂ hq₂.1 p ⟨hp, hp₂⟩).mpr h1)
    rcases isPreconnected_iff_subset_of_disjoint.mp hfc u v huo hvo hcov hdisj with h | h
    · intro p hp
      obtain ⟨q₁, hq₁, hp₁⟩ := mem_iUnion₂.mp (h hp)
      exact (hiff x hx q₁ hq₁.1 p ⟨hp, hp₁⟩).mp hq₁.2
    · exfalso
      obtain ⟨q₀, hq₀, hq₀cl⟩ := exists_frontier_mem_closure_connectedComponentIn hΩo hne hx
      obtain ⟨q₂, hq₂, hp₂⟩ := mem_iUnion₂.mp (h hq₀)
      exact hq₂.2 ((hiff x hx q₂ hq₂.1 q₀ ⟨hq₀, hp₂⟩).mpr hq₀cl)
  -- a point of the exterior
  obtain ⟨R, hR⟩ := hb.closure.subset_ball (0 : ℂ)
  set x₀ : ℂ := ((|R| + 1 : ℝ) : ℂ) with hx₀
  have hx₀E : x₀ ∈ E := by
    intro h
    have h1 := mem_ball_zero_iff.mp (hR h)
    rw [hx₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
    linarith [le_abs_self R]
  have hsub : E ⊆ connectedComponentIn E x₀ := by
    intro y hy
    obtain ⟨q, hq, hqcl⟩ := exists_frontier_mem_closure_connectedComponentIn hΩo hne hy
    have h1 := hK x₀ hx₀E q hq q (hqV q hq) (hall x₀ hx₀E hq)
    have h2 := hK y hy q hq q (hqV q hq) hqcl
    obtain ⟨b, hb⟩ : (B q).Nonempty :=
      closure_nonempty_iff.mp ⟨q, hcl q hq q ⟨hq, hqV q hq⟩⟩
    rw [connectedComponentIn_eq (h1 hb), ← connectedComponentIn_eq (h2 hb)]
    exact mem_connectedComponentIn hy
  have heq : E = connectedComponentIn E x₀ :=
    Subset.antisymm hsub (connectedComponentIn_subset E x₀)
  refine ⟨⟨x₀, hx₀E⟩, ?_⟩
  rw [heq]
  exact isPreconnected_connectedComponentIn

end PolyaNeumann

end
