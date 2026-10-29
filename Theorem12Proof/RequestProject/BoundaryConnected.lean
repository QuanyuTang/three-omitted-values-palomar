module

public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Topology.Homotopy.Lifting
public import Theorem12Proof.RequestProject.BoundaryLoop
public import Theorem12Proof.RequestProject.ExteriorConnected

/-!
# The boundary of a simply connected Lipschitz domain is connected

Let `Ω` be a bounded simply connected Lipschitz domain.

* For `z ∉ Ω̄`, the function `w ↦ w - z` has a continuous logarithm on `Ω` (lifting through the
  covering map `exp`, which uses simple connectivity), and this logarithm extends continuously to
  `Ω̄`, because near a boundary point `Ω` is the connected region above a Lipschitz graph
  (`exists_log_closure`). Hence every closed Lipschitz curve in `Ω̄` has winding number `0` about
  every point outside `Ω̄` (`windingNumber_eq_zero_of_lift`).
* A Lipschitz Jordan loop `γ` contained in `∂Ω` (from the boundary walk) separates a point of `Ω`
  from a point outside `Ω̄` near one of its points: the winding numbers differ by the jump `±1`
  (`exists_windingNumber_ne_of_frontier`).
* If `∂Ω` had a point `q` off the loop, then near `q` there would be both points of `Ω` and points
  outside `Ω̄` in a disc missing the loop, so the winding number of the loop would be `0` on `Ω`,
  contradicting the jump. Hence the loop is all of `∂Ω`, and `∂Ω` is connected
  (`isPreconnected_frontier_of_simplyConnected`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- If a closed Lipschitz curve avoiding `z` has a continuous logarithm of `γ - z` taking the same
value at both ends, its winding number about `z` vanishes. -/
theorem windingNumber_eq_zero_of_lift {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {z : ℂ} (hz : ∀ θ ∈ Icc 0 (2 * π), γ θ ≠ z) {G : ℝ → ℂ}
    (hG : ContinuousOn G (Icc 0 (2 * π)))
    (hexp : ∀ θ ∈ Icc 0 (2 * π), Complex.exp (G θ) = γ θ - z) (hG2 : G (2 * π) = G 0) :
    windingNumber γ z = 0 := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  set I : ℝ → ℂ := fun θ => ∫ t in (0 : ℝ)..θ, deriv γ t / (γ t - z) with hI
  have hint := intervalIntegrable_deriv_div hK h2π hz
  have hIc : ContinuousOn I (Icc 0 (2 * π)) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (f := fun t => deriv γ t / (γ t - z)) (a := 0) (b := 2 * π)
      (by rw [uIcc_of_le h2π]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le h2π).mp hint)
    rwa [uIcc_of_le h2π] at this
  have hexpI := exp_neg_integral_mul_eq hK h2π hz
  have h0 : γ 0 - z ≠ 0 := sub_ne_zero.mpr (hz 0 ⟨le_rfl, h2π⟩)
  set D : ℝ → ℂ := fun θ => (G θ - I θ - G 0) / (2 * π * Complex.I) with hD
  have hDint : ∀ θ ∈ Icc 0 (2 * π), D θ ∈ range ((↑) : ℤ → ℂ) := by
    intro θ hθ
    have hexp1 : Complex.exp (G θ - I θ - G 0) = 1 := by
      rw [sub_eq_add_neg (G θ - I θ), sub_eq_add_neg, Complex.exp_add, Complex.exp_add,
        Complex.exp_neg (G 0), hexp θ hθ, hexp 0 ⟨le_rfl, h2π⟩]
      have := hexpI θ hθ
      field_simp
      rw [mul_comm] at this
      linear_combination this
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
    refine ⟨n, ?_⟩
    simp only [hD]
    rw [hn]
    field_simp
  have hDc : ContinuousOn D (Icc 0 (2 * π)) :=
    ((hG.sub hIc).sub continuousOn_const).div_const _
  have hconst := isPreconnected_Icc.constant_of_mapsTo
    (isDiscrete_iff_discreteTopology.mpr inferInstance) hDc hDint
    (⟨h2π, le_rfl⟩ : 2 * π ∈ Icc 0 (2 * π)) (⟨le_rfl, h2π⟩ : (0 : ℝ) ∈ Icc 0 (2 * π))
  have hD0 : D 0 = 0 := by simp [hD, hI]
  rw [hD0] at hconst
  simp only [hD, div_eq_zero_iff, mul_eq_zero, Complex.I_ne_zero, or_false] at hconst
  have hI2 : I (2 * π) = 0 := by
    rcases hconst with h | h
    · rw [hG2] at h; linear_combination -h
    · exfalso; norm_num [Real.pi_ne_zero] at h
  simp only [windingNumber]
  rw [show (∫ θ in (0 : ℝ)..(2 * π), deriv γ θ / (γ θ - z)) = I (2 * π) from rfl, hI2, mul_zero]

/-- Small charts: every boundary point of a Lipschitz domain has charts with arbitrarily small
boxes. -/
lemma exists_small_chart {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) {p : ℂ} (hp : p ∈ frontier Ω)
    {d : ℝ} (hd : 0 < d) : ∃ (c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ),
      IsChartAt Ω p c r h K f ∧ chartBox p c r h ⊆ ball p d := by
  obtain ⟨c, r, h, K, f, hch⟩ := hL.exists_chart hp
  have hr := hch.2.1
  have hh := hch.2.2.1
  set H' := min (h / 2) (d / 2) with hH'
  have hH'0 : 0 < H' := lt_min (by linarith) (by linarith)
  set ρ' := min (r / 2) (H' / (2 * (K + 1))) with hρ'
  have hρ'0 : 0 < ρ' := lt_min (by linarith) (by positivity)
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  have hρ'H : ρ' ≤ H' / (2 * (K + 1)) := min_le_right _ _
  have hKρ : (K : ℝ) * ρ' < H' := by
    calc (K : ℝ) * ρ' ≤ K * (H' / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hρ'H hK0
      _ < H' := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hp0 : c * (p - p) = 0 := by simp
  have hrec := isChartAt_recenter hL.1.1 hch hp (by rw [hp0]; simp; linarith)
    (by rw [hp0]; simp; linarith) hρ'0 hH'0 (min_le_left _ _) (min_le_left _ _) le_rfl hKρ
  refine ⟨c, ρ', H', K, _, hrec, fun w hw => ?_⟩
  rw [mem_ball, dist_eq_norm, ← norm_mul_sub hch.1]
  have h1 := Complex.norm_le_abs_re_add_abs_im (c * (w - p))
  have h2 : ρ' ≤ H' / 2 := by
    have : H' / (2 * (K + 1)) ≤ H' / 2 :=
      div_le_div_of_nonneg_left hH'0.le (by norm_num) (by linarith)
    linarith
  have h3 : H' ≤ d / 2 := min_le_right _ _
  linarith [hw.1, hw.2]

/-- In a chart box, the part of `Ω` (the region above the graph) is preconnected. -/
lemma isPreconnected_chart_inter {Ω : Set ℂ} {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) : IsPreconnected (Ω ∩ chartBox p c r h) := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  have hcc : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  set Φ : ℝ × ℝ → ℂ := fun q =>
    p + conj c * ((q.1 : ℂ) + ((f q.1 + q.2 * (h - f q.1) : ℝ) : ℂ) * Complex.I) with hΦ
  have hcoord : ∀ q : ℝ × ℝ, c * (Φ q - p) =
      (q.1 : ℂ) + ((f q.1 + q.2 * (h - f q.1) : ℝ) : ℂ) * Complex.I := fun q => by
    simp only [hΦ, add_sub_cancel_left, ← mul_assoc, hcc, one_mul]
  have hre : ∀ q : ℝ × ℝ, (c * (Φ q - p)).re = q.1 := fun q => by rw [hcoord]; simp
  have him : ∀ q : ℝ × ℝ, (c * (Φ q - p)).im = f q.1 + q.2 * (h - f q.1) := fun q => by
    rw [hcoord]; simp
  have hset : Ω ∩ chartBox p c r h = Φ '' (Ioo (-r) r ×ˢ Ioo 0 1) := by
    ext w
    constructor
    · rintro ⟨hwΩ, hw1, hw2⟩
      set X := (c * (w - p)).re
      set Y := (c * (w - p)).im
      have hfX := (abs_lt.mp (hfb X hw1))
      have hlt : f X < Y := (hΩ w hw1 hw2).mp hwΩ
      have hY := abs_lt.mp hw2
      have hpos : 0 < h - f X := by linarith
      refine ⟨(X, (Y - f X) / (h - f X)), ⟨abs_lt.mp hw1, div_pos (by linarith) hpos,
        (div_lt_one hpos).mpr (by linarith)⟩, ?_⟩
      refine eq_of_re_im_eq (p := p) hc ?_ ?_
      · rw [hre]
      · rw [him]; simp only; field_simp; ring
    · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
      have hfq := abs_lt.mp (hfb q.1 (abs_lt.mpr hq1))
      have h1 : |(c * (Φ q - p)).re| < r := by rw [hre]; exact abs_lt.mpr hq1
      have hpos : 0 < h - f q.1 := by linarith
      have hm1 : 0 < q.2 * (h - f q.1) := mul_pos hq2.1 hpos
      have hm2 : q.2 * (h - f q.1) < h - f q.1 := by nlinarith [hq2.2]
      have h2 : |(c * (Φ q - p)).im| < h := by
        rw [him, abs_lt]; constructor <;> linarith
      refine ⟨(hΩ _ h1 h2).mpr ?_, h1, h2⟩
      rw [hre, him]; linarith
  rw [hset]
  refine (isPreconnected_Ioo.prod isPreconnected_Ioo).image Φ ?_
  have : Continuous Φ := by
    simp only [hΦ]
    have := hf.continuous
    fun_prop
  exact this.continuousOn

/-- **Logarithms on the closure.** For a simply connected Lipschitz domain `Ω` and `z ∉ Ω̄`,
`w ↦ w - z` has a logarithm that is continuous on `Ω̄`. -/
theorem exists_log_closure {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω)
    {z : ℂ} (hz : z ∉ closure Ω) :
    ∃ L : ℂ → ℂ, ContinuousOn L (closure Ω) ∧ ∀ w ∈ closure Ω, Complex.exp (L w) = w - z := by
  classical
  have hΩo := hL.1.1
  have hzΩ : z ∉ Ω := fun h => hz (subset_closure h)
  letI : LocallyPathConnectedSpace Ω := hΩo.locallyPathConnectedSpace
  letI : SimplyConnectedSpace Ω := hsc
  obtain ⟨w₀, hw₀⟩ := hL.1.2.nonempty
  have hw₀z : w₀ - z ≠ 0 := sub_ne_zero.mpr fun h => hzΩ (h ▸ hw₀)
  -- a continuous logarithm on `Ω`, by lifting through `exp`
  set fΩ : C(Ω, ℂ) := ⟨fun w => (w : ℂ) - z, by fun_prop⟩ with hfΩ
  have hne : ∀ a : Ω, fΩ a ∈ ({0}ᶜ : Set ℂ) := fun a => by
    simp only [hfΩ, ContinuousMap.coe_mk, mem_compl_iff, mem_singleton_iff]
    exact sub_ne_zero.mpr fun h => hzΩ (h ▸ a.2)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts fΩ
    (a₀ := ⟨w₀, hw₀⟩) (e₀ := Complex.log (w₀ - z)) (by simp [hfΩ, Complex.exp_log hw₀z]) hne
  set L₀ : ℂ → ℂ := fun w => if h : w ∈ Ω then F ⟨w, h⟩ else 0 with hL₀
  have hL₀exp : ∀ w ∈ Ω, Complex.exp (L₀ w) = w - z := fun w hw => by
    simp only [hL₀, dif_pos hw]
    exact congrFun hF ⟨w, hw⟩
  have hL₀c : ContinuousOn L₀ Ω := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : Ω.domRestrict L₀ = F := funext fun a => by simp [Set.domRestrict, hL₀, a.2]
    rw [this]; exact F.continuous
  -- local branches at boundary points agreeing with `L₀` on `Ω`
  have hloc : ∀ p ∈ frontier Ω, ∃ U : Set ℂ, IsOpen U ∧ p ∈ U ∧ ∃ ℓ : ℂ → ℂ,
      ContinuousOn ℓ U ∧ (∀ w ∈ U, Complex.exp (ℓ w) = w - z) ∧ EqOn L₀ ℓ (Ω ∩ U) := by
    intro p hp
    have hpz : p - z ≠ 0 := sub_ne_zero.mpr fun h => hz (h ▸ frontier_subset_closure hp)
    have hd : 0 < ‖p - z‖ := norm_pos_iff.mpr hpz
    obtain ⟨c, r, h, K, f, hch, hball⟩ := exists_small_chart hL hp hd
    set B := chartBox p c r h
    have hBo : IsOpen B := isOpen_chartBox _ _ _ _
    have hslit : ∀ w ∈ B, (w - z) / (p - z) ∈ Complex.slitPlane := fun w hw => by
      have hw' := hball hw
      rw [mem_ball, dist_eq_norm] at hw'
      have : (w - z) / (p - z) = 1 + (w - p) / (p - z) := by field_simp; ring
      rw [this]
      refine Or.inl ?_
      have h1 : ‖(w - p) / (p - z)‖ < 1 := by
        rw [norm_div, div_lt_one hd]; exact hw'
      have h2 := Complex.abs_re_le_norm ((w - p) / (p - z))
      rw [Complex.add_re, Complex.one_re]
      linarith [neg_abs_le ((w - p) / (p - z)).re]
    set ℓ₁ : ℂ → ℂ := fun w => Complex.log ((w - z) / (p - z)) + Complex.log (p - z) with hℓ₁
    have hℓ₁c : ContinuousOn ℓ₁ B :=
      ((ContinuousOn.clog (by fun_prop) hslit).add continuousOn_const)
    have hℓ₁exp : ∀ w ∈ B, Complex.exp (ℓ₁ w) = w - z := fun w hw => by
      simp only [hℓ₁, Complex.exp_add]
      rw [Complex.exp_log (Complex.slitPlane_ne_zero (hslit w hw)), Complex.exp_log hpz]
      field_simp
    obtain ⟨w₁, hw₁B, hw₁Ω⟩ : (B ∩ Ω).Nonempty :=
      mem_closure_iff.mp (frontier_subset_closure hp) B hBo hch.center_mem_box
    set D : ℂ → ℂ := fun w => (L₀ w - ℓ₁ w) / (2 * π * Complex.I) with hD
    have hDint : ∀ w ∈ Ω ∩ B, D w ∈ range ((↑) : ℤ → ℂ) := by
      intro w hw
      have hexp1 : Complex.exp (L₀ w - ℓ₁ w) = 1 := by
        rw [Complex.exp_sub, hL₀exp w hw.1, hℓ₁exp w hw.2]
        exact div_self (sub_ne_zero.mpr fun h => hzΩ (h ▸ hw.1))
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
      exact ⟨n, by simp only [hD]; rw [hn]; field_simp⟩
    have hDc : ContinuousOn D (Ω ∩ B) :=
      ((hL₀c.mono inter_subset_left).sub (hℓ₁c.mono inter_subset_right)).div_const _
    have hconst : ∀ x ∈ Ω ∩ B, ∀ y ∈ Ω ∩ B, D x = D y := fun x hx y hy =>
      (isPreconnected_chart_inter hch).constant_of_mapsTo
        (isDiscrete_iff_discreteTopology.mpr inferInstance) hDc hDint hx hy
    have hw₁z : w₁ - z ≠ 0 := by
      intro h; apply hzΩ; rw [← sub_eq_zero.mp h]; exact hw₁Ω
    refine ⟨B, hBo, hch.center_mem_box, fun w => ℓ₁ w + (L₀ w₁ - ℓ₁ w₁),
      hℓ₁c.add continuousOn_const, fun w hw => ?_, fun w hw => ?_⟩
    · rw [Complex.exp_add, hℓ₁exp w hw, Complex.exp_sub, hL₀exp w₁ hw₁Ω, hℓ₁exp w₁ hw₁B,
        div_self hw₁z, mul_one]
    · have := hconst w hw w₁ ⟨hw₁Ω, hw₁B⟩
      simp only [hD] at this
      have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have := (div_left_inj' h2).mp this
      simp only
      linear_combination this
  choose! U hUo hpU ℓ hℓc hℓexp hℓeq using hloc
  -- consistency of the local branches at boundary points
  have hcons : ∀ p ∈ frontier Ω, ∀ w ∈ frontier Ω ∩ U p, ℓ w w = ℓ p w := by
    intro p hp w hw
    set S := Ω ∩ (U w ∩ U p)
    have hUw : U w ∩ U p ∈ 𝓝 w := ((hUo w hw.1).inter (hUo p hp)).mem_nhds ⟨hpU w hw.1, hw.2⟩
    have hwS : w ∈ closure S := by
      rw [mem_closure_iff_nhds]
      intro t ht
      obtain ⟨x, hxt, hxΩ⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hw.1) _
        (Filter.inter_mem ht hUw)
      exact ⟨x, hxt.1, hxΩ, hxt.2⟩
    haveI := mem_closure_iff_nhdsWithin_neBot.mp hwS
    have h1 : Tendsto (ℓ w) (𝓝[S] w) (𝓝 (ℓ w w)) :=
      (((hℓc w hw.1).continuousAt ((hUo w hw.1).mem_nhds (hpU w hw.1))).tendsto).mono_left
        nhdsWithin_le_nhds
    have h2 : Tendsto (ℓ p) (𝓝[S] w) (𝓝 (ℓ p w)) :=
      (((hℓc p hp).continuousAt ((hUo p hp).mem_nhds hw.2)).tendsto).mono_left
        nhdsWithin_le_nhds
    have heq : ℓ w =ᶠ[𝓝[S] w] ℓ p := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [← hℓeq w hw.1 ⟨hx.1, hx.2.1⟩, hℓeq p hp ⟨hx.1, hx.2.2⟩]
    exact tendsto_nhds_unique (h1.congr' heq) h2
  set L : ℂ → ℂ := fun w => if w ∈ Ω then L₀ w else ℓ w w with hLdef
  have hfr : ∀ w ∈ closure Ω, w ∉ Ω → w ∈ frontier Ω := fun w h1 h2 => by
    rw [hΩo.frontier_eq]; exact ⟨h1, h2⟩
  have hLeq : ∀ p ∈ frontier Ω, EqOn L (ℓ p) (closure Ω ∩ U p) := by
    intro p hp w hw
    by_cases hwΩ : w ∈ Ω
    · simp only [hLdef, if_pos hwΩ]; exact hℓeq p hp ⟨hwΩ, hw.2⟩
    · simp only [hLdef, if_neg hwΩ]; exact hcons p hp w ⟨hfr w hw.1 hwΩ, hw.2⟩
  refine ⟨L, fun w hw => ?_, fun w hw => ?_⟩
  · by_cases hwΩ : w ∈ Ω
    · refine ContinuousAt.continuousWithinAt ?_
      refine (hL₀c.continuousAt (hΩo.mem_nhds hwΩ)).congr ?_
      filter_upwards [hΩo.mem_nhds hwΩ] with x hx
      simp only [hLdef, if_pos hx]
    · have hwf := hfr w hw hwΩ
      refine ContinuousWithinAt.congr_of_eventuallyEq
        ((hℓc w hwf).continuousAt ((hUo w hwf).mem_nhds (hpU w hwf))).continuousWithinAt ?_
        (hLeq w hwf ⟨hw, hpU w hwf⟩)
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds ((hUo w hwf).mem_nhds (hpU w hwf))] with x hx1 hx2
      exact hLeq w hwf ⟨hx1, hx2⟩
  · by_cases hwΩ : w ∈ Ω
    · simp only [hLdef, if_pos hwΩ]; exact hL₀exp w hwΩ
    · have hwf := hfr w hw hwΩ
      simp only [hLdef, if_neg hwΩ]
      exact hℓexp w hwf w (hpU w hwf)

/-- A periodic curve takes all its values on `[0, 2π]`. -/
lemma mem_image_Icc_of_periodic {γ : ℝ → ℂ} (hper : Function.Periodic γ (2 * π)) (θ : ℝ) :
    γ θ ∈ γ '' Icc 0 (2 * π) := by
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  rw [← hper.sub_zsmul_eq (toIcoDiv h2pi 0 θ)]
  refine mem_image_of_mem γ ?_
  have := toIcoMod_mem_Ico h2pi 0 θ
  rw [zero_add] at this
  exact ⟨this.1, this.2.le⟩

/-- **The jump across a boundary loop.** A Lipschitz `2π`-periodic curve, injective on
`[0, 2π)`, with image in `∂Ω`, has different winding numbers about some point of `Ω` and some
point outside `Ω̄`. -/
theorem exists_windingNumber_ne_of_frontier {Ω : Set ℂ} (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hper : Function.Periodic γ (2 * π))
    (hinj : InjOn γ (Ico 0 (2 * π))) (hsub : γ '' Icc 0 (2 * π) ⊆ frontier Ω) :
    ∃ z₁ ∈ Ω, ∃ z₂, z₂ ∉ closure Ω ∧ windingNumber γ z₁ ≠ windingNumber γ z₂ := by
  have hpi : 0 < π := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hΩo : IsOpen Ω := hL.1.1
  have hfront : ∀ θ, γ θ ∈ frontier Ω := fun θ => hsub (mem_image_Icc_of_periodic hper θ)
  set p := γ 0 with hpdef
  obtain ⟨c, r, h, K', f, hc, hr, hh, hf, hf0, -, hΩ⟩ := hL.2 p (hfront 0)
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hc; exact zero_ne_one hc
  set γ' : ℝ → ℂ := fun θ => c * (γ θ - p) with hγ'
  have hK' : LipschitzWith K γ' := LipschitzWith.of_dist_le_mul fun x y => by
    simp only [hγ', dist_eq_norm, ← mul_sub, norm_mul, hc, one_mul, sub_sub_sub_cancel_right]
    rw [← dist_eq_norm]
    exact hK.dist_le_mul x y
  have hper' : Function.Periodic γ' (2 * π) := fun θ => by simp only [hγ', hper θ]
  have h0' : γ' 0 = 0 := by simp [hγ', hpdef]
  set m := min r h with hm
  have hm0 : 0 < m := lt_min hr hh
  set η := min (π / 2) (m / (2 * (K + 1))) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hηπ2 : η ≤ π / 2 := min_le_left _ _
  have hηπ : η < π := hηπ2.trans_lt (by linarith)
  have hsmall : ∀ θ ∈ Icc (-η) η, ‖γ' θ‖ < m := by
    intro θ hθ
    have h1 : ‖γ' θ‖ ≤ K * |θ| := by
      have := hK'.dist_le_mul θ 0
      rwa [h0', dist_zero_right, Real.dist_eq, sub_zero] at this
    have h2 : |θ| ≤ η := abs_le.mpr ⟨hθ.1, hθ.2⟩
    have h3 : (K : ℝ) * η ≤ K * (m / (2 * (K + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) K.coe_nonneg
    have h4 : (K : ℝ) * (m / (2 * (K + 1))) < m := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [K.coe_nonneg]
    calc ‖γ' θ‖ ≤ K * |θ| := h1
      _ ≤ K * η := mul_le_mul_of_nonneg_left h2 K.coe_nonneg
      _ < m := h3.trans_lt h4
  have hbox : ∀ θ ∈ Icc (-η) η, |(γ' θ).re| < r ∧ |(γ' θ).im| < h := fun θ hθ =>
    ⟨(Complex.abs_re_le_norm _).trans_lt ((hsmall θ hθ).trans_le (min_le_left _ _)),
      (Complex.abs_im_le_norm _).trans_lt ((hsmall θ hθ).trans_le (min_le_right _ _))⟩
  have hgraph : ∀ θ ∈ Icc (-η) η, (γ' θ).im = f (γ' θ).re := fun θ hθ =>
    chart_frontier_graph hΩo hf hΩ (hfront θ) (hbox θ hθ).1 (hbox θ hθ).2
  have hinj' : InjOn γ' (Icc (-η) η) := by
    intro θ₁ h₁ θ₂ h₂ he
    have he' : γ θ₁ = γ θ₂ := by
      have := mul_left_cancel₀ hc0 he
      simpa using this
    have hmod : ∀ θ, γ (toIcoMod h2pi 0 θ) = γ θ := fun θ => hper.sub_zsmul_eq _
    have hmem : ∀ θ, toIcoMod h2pi 0 θ ∈ Ico 0 (2 * π) := fun θ => by
      have := toIcoMod_mem_Ico h2pi 0 θ
      rwa [zero_add] at this
    have heq := hinj (hmem θ₁) (hmem θ₂) (by rw [hmod, hmod, he'])
    obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod h2pi).mp heq
    rw [zsmul_eq_mul] at hn
    have hb1 : θ₂ - θ₁ ≤ π := by linarith [h₁.1, h₂.2]
    have hb2 : -π ≤ θ₂ - θ₁ := by linarith [h₁.2, h₂.1]
    have hn1 : (n : ℝ) < 1 := by nlinarith
    have hn2 : (-1 : ℝ) < n := by nlinarith
    have hn0 : n = 0 := by
      have := Int.cast_lt.mp (show ((n : ℤ) : ℝ) < ((1 : ℤ) : ℝ) by simpa using hn1)
      have := Int.cast_lt.mp (show ((-1 : ℤ) : ℝ) < ((n : ℤ) : ℝ) by simpa using hn2)
      omega
    rw [hn0, Int.cast_zero, zero_mul, sub_eq_zero] at hn
    exact hn.symm
  have hfar' : ∀ θ ∈ Icc η (2 * π - η), γ' θ ≠ 0 := by
    intro θ hθ h0
    have hγθ : γ θ = γ 0 := by
      have := mul_eq_zero.mp h0
      rcases this with h1 | h1
      · exact absurd h1 hc0
      · exact sub_eq_zero.mp h1
    have := hinj ⟨by linarith [hθ.1], by linarith [hθ.2]⟩ ⟨le_rfl, h2pi⟩ hγθ
    linarith [hθ.1]
  obtain ⟨σ', hσ', hlim⟩ := windingNumber_jump hK' hper' hη0 hηπ h0' hgraph hinj' hfar'
  have hcz : ∀ x : ℂ, c * (p + c⁻¹ * x - p) = x := fun x => by field_simp; ring
  have hσ0 : σ' ≠ 0 := by rcases hσ' with h1 | h1 <;> simp [h1]
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 0, windingNumber γ' ((s : ℂ) * Complex.I) -
      windingNumber γ' (-((s : ℂ) * Complex.I)) ≠ 0 :=
    hlim.eventually (isOpen_ne.mem_nhds hσ0)
  obtain ⟨s, hsne, hs⟩ := (hev.and (Ioo_mem_nhdsGT hh)).exists
  rw [windingNumber_affine γ hc0, windingNumber_affine γ hc0] at hsne
  have hin' : p + c⁻¹ * ((s : ℂ) * Complex.I) ∈ Ω := by
    rw [hΩ _ (by rw [hcz]; simpa using hr) (by rw [hcz]; simpa [abs_of_pos hs.1] using hs.2),
      hcz]
    simpa [hf0] using hs.1
  have hout' : p + c⁻¹ * (-((s : ℂ) * Complex.I)) ∉ closure Ω := by
    refine chart_notMem_closure hf hΩ (by rw [hcz]; simpa using hr)
      (by rw [hcz]; simpa [abs_of_pos hs.1] using hs.2) ?_
    rw [hcz]
    simpa [hf0] using hs.1
  exact ⟨_, hin', _, hout', sub_ne_zero.mp hsne⟩

/-- Boundary points of a Lipschitz domain are limits of exterior points. -/
lemma mem_closure_compl_closure {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) {q : ℂ}
    (hq : q ∈ frontier Ω) : q ∈ closure (closure Ω)ᶜ := by
  obtain ⟨V, B, -, hqV, -, hB, -, hcl⟩ := exists_exterior_box hL hq
  exact closure_mono hB (hcl q ⟨hq, hqV⟩)

/-- **External theorem E3, connectedness of the boundary.** The boundary of a bounded simply
connected Lipschitz domain is connected. -/
theorem isPreconnected_frontier_of_simplyConnected {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    IsPreconnected (frontier Ω) := by
  by_contra hnc
  obtain ⟨γ, ⟨K, hK⟩, hper, hinj, hsub, -⟩ := exists_jordanLoop_frontier hb hL
  have hclosed : γ (2 * π) = γ 0 := by simpa using hper 0
  set S := γ '' Icc 0 (2 * π) with hS
  obtain ⟨q, hqf, hqS⟩ : ∃ q ∈ frontier Ω, q ∉ S := by
    by_contra hall
    push_neg at hall
    exact hnc (subset_antisymm hsub hall ▸ isPreconnected_Icc.image γ hK.continuous.continuousOn)
  have hγcl : ∀ θ, γ θ ∈ closure Ω := fun θ =>
    frontier_subset_closure (hsub (mem_image_Icc_of_periodic hper θ))
  -- winding numbers vanish outside the closure
  have hzero : ∀ z, z ∉ closure Ω → windingNumber γ z = 0 := fun z hz => by
    obtain ⟨L, hLc, hLexp⟩ := exists_log_closure hL hsc hz
    refine windingNumber_eq_zero_of_lift hK (G := L ∘ γ)
      (fun θ _ h => hz (h ▸ hγcl θ))
      (hLc.comp hK.continuous.continuousOn fun θ _ => hγcl θ)
      (fun θ _ => hLexp _ (hγcl θ)) (by simp only [Function.comp, hclosed])
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := exists_windingNumber_ne_of_frontier hL hK hper hinj hsub
  -- a disc around `q` missing the loop
  have hSc : IsClosed S := (isCompact_Icc.image hK.continuous).isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hSc.isOpen_compl q hqS
  have hdisj : Disjoint (ball q ε) S := disjoint_left.mpr fun x hx hxS => hball hx hxS
  obtain ⟨a, haΩ, haB⟩ := mem_closure_iff.mp (frontier_subset_closure hqf) ε hε
  obtain ⟨b, hbΩ, hbB⟩ := mem_closure_iff.mp (mem_closure_compl_closure hL hqf) ε hε
  have hab : windingNumber γ a = windingNumber γ b :=
    windingNumber_const_of_isPreconnected hK hclosed (convex_ball q ε).isPreconnected hdisj
      (by rw [mem_ball, dist_comm]; exact haB) (by rw [mem_ball, dist_comm]; exact hbB)
  have hΩS : Disjoint Ω S := by
    refine disjoint_left.mpr fun x hx hxS => ?_
    have := hsub hxS
    rw [hL.1.1.frontier_eq] at this
    exact this.2 hx
  have ha1 : windingNumber γ z₁ = windingNumber γ a :=
    windingNumber_const_of_isPreconnected hK hclosed hL.1.2.isPreconnected hΩS hz₁ haΩ
  exact hne (by rw [ha1, hab, hzero b hbΩ, hzero z₂ hz₂])

end PolyaNeumann
