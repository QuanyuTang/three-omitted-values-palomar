module

public import Theorem12Proof.RequestProject.WindingJump

/-!
# Orientation of a Lipschitz Jordan boundary

Let `Ω` be a bounded Lipschitz domain and `γ` a Lipschitz, `2π`-periodic parametrization of
`∂Ω`, injective on `[0, 2π)`, such that the exterior `ℂ \ Ω̄` is connected. Then the winding
number of `γ` is a constant `σ = ±1` on `Ω` and vanishes off `Ω̄`
(`windingNumber_pm_one_of_jordan`). The value `±1` comes from the jump of the winding number
across the boundary at a chart point (`windingNumber_jump`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- In a Lipschitz chart box, points strictly below the graph are not in the closure. -/
lemma chart_notMem_closure {Ω : Set ℂ} {c p : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith K f)
    (hΩ : ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im))
    {w : ℂ} (hr : |(c * (w - p)).re| < r) (hh : |(c * (w - p)).im| < h)
    (hlt : (c * (w - p)).im < f (c * (w - p)).re) : w ∉ closure Ω := by
  have hg : Continuous fun v : ℂ => c * (v - p) := by fun_prop
  set U : Set ℂ := {v | |(c * (v - p)).re| < r} ∩ {v | |(c * (v - p)).im| < h} ∩
    {v | (c * (v - p)).im < f (c * (v - p)).re} with hU
  have hUo : IsOpen U := by
    refine ((isOpen_lt ?_ continuous_const).inter (isOpen_lt ?_ continuous_const)).inter
      (isOpen_lt ?_ ?_)
    · exact (Complex.continuous_re.comp hg).abs
    · exact (Complex.continuous_im.comp hg).abs
    · exact Complex.continuous_im.comp hg
    · exact hf.continuous.comp (Complex.continuous_re.comp hg)
  have hdisj : Disjoint U Ω := by
    rw [Set.disjoint_left]
    rintro v ⟨⟨hv1, hv2⟩, hv3⟩ hvΩ
    exact absurd ((hΩ v hv1 hv2).mp hvΩ) (not_lt.mpr hv3.le)
  exact fun hw => Set.disjoint_left.mp (hdisj.closure_right hUo) ⟨⟨hr, hh⟩, hlt⟩ hw

/-- In a Lipschitz chart box, boundary points lie on the graph. -/
lemma chart_frontier_graph {Ω : Set ℂ} (hΩo : IsOpen Ω) {c p : ℂ} {r h : ℝ} {K : NNReal}
    {f : ℝ → ℝ} (hf : LipschitzWith K f)
    (hΩ : ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im))
    {w : ℂ} (hw : w ∈ frontier Ω) (hr : |(c * (w - p)).re| < r)
    (hh : |(c * (w - p)).im| < h) : (c * (w - p)).im = f (c * (w - p)).re := by
  rw [hΩo.frontier_eq] at hw
  have h1 : (c * (w - p)).im ≤ f (c * (w - p)).re :=
    not_lt.mp fun hlt => hw.2 ((hΩ w hr hh).mpr hlt)
  refine le_antisymm h1 (not_lt.mp fun hlt => ?_)
  exact chart_notMem_closure hf hΩ hr hh hlt hw.1

/-- The winding number under a rigid motion `w ↦ c (w - p)` (`c ≠ 0`). -/
lemma windingNumber_affine (γ : ℝ → ℂ) {c : ℂ} (hc : c ≠ 0) (p w : ℂ) :
    windingNumber (fun θ => c * (γ θ - p)) w = windingNumber γ (p + c⁻¹ * w) := by
  unfold windingNumber
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hd : deriv (fun θ => c * (γ θ - p)) θ = c * deriv γ θ := by
    rw [deriv_const_mul_field']
    exact congrArg _ (deriv_sub_const p)
  have he : c * (γ θ - p) - w = c * (γ θ - (p + c⁻¹ * w)) := by
    field_simp
    ring
  simp only [hd, he]
  exact mul_div_mul_left _ _ hc

/-- **Orientation of a Lipschitz Jordan boundary.** For a bounded Lipschitz domain `Ω` with a
Lipschitz `2π`-periodic boundary parametrization `γ`, injective on `[0, 2π)`, and connected
exterior `ℂ \ Ω̄`, the winding number of `γ` is a constant `σ = ±1` on `Ω` and vanishes off
`Ω̄`. -/
theorem windingNumber_pm_one_of_jordan {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ (2 * π)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * π)))
    (him : γ '' Set.Icc 0 (2 * π) = frontier Ω) (hext : IsConnected (closure Ω)ᶜ) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (∀ z ∈ Ω, windingNumber γ z = σ) ∧
      ∀ z, z ∉ closure Ω → windingNumber γ z = 0 := by
  have hpi : 0 < π := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hclosed : γ (2 * π) = γ 0 := by simpa using hper 0
  have hΩo : IsOpen Ω := hL.1.1
  have hΩdisj : Disjoint Ω (γ '' Set.Icc 0 (2 * π)) := by
    rw [him, Set.disjoint_iff_inter_eq_empty]
    exact hΩo.inter_frontier_eq
  obtain ⟨z₀, hz₀⟩ := hL.1.2.nonempty
  have hin : ∀ z ∈ Ω, windingNumber γ z = windingNumber γ z₀ := fun z hz =>
    windingNumber_const_of_isPreconnected hK hclosed hL.1.2.isPreconnected hΩdisj hz hz₀
  -- the winding number vanishes on the exterior
  obtain ⟨R, hR⟩ := hb.closure.subset_ball (0 : ℂ)
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z₀)
    (mem_ball_zero_iff.mp (hR (subset_closure hz₀))).le
  set w : ℂ := ((R + K + 1 : ℝ) : ℂ) with hw
  have hwn : ‖w‖ = R + K + 1 := by
    rw [hw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hwext : w ∉ closure Ω := fun h => by
    have := mem_ball_zero_iff.mp (hR h); linarith [K.coe_nonneg]
  have hw0 : windingNumber γ w = 0 := by
    refine windingNumber_eq_zero_of_far hK hclosed (d := K + 1) (by linarith) fun θ hθ => ?_
    have hγθ : ‖γ θ‖ < R :=
      mem_ball_zero_iff.mp (hR (frontier_subset_closure (him ▸ Set.mem_image_of_mem γ hθ)))
    have := norm_sub_norm_le w (γ θ)
    rw [norm_sub_rev] at this
    linarith
  have hextdisj : Disjoint (closure Ω)ᶜ (γ '' Set.Icc 0 (2 * π)) := by
    rw [him]
    exact (disjoint_compl_left (a := closure Ω)).mono_right frontier_subset_closure
  have hout : ∀ z, z ∉ closure Ω → windingNumber γ z = 0 := fun z hz =>
    (windingNumber_const_of_isPreconnected hK hclosed hext.isPreconnected hextdisj hz
      hwext).trans hw0
  -- a chart at `p = γ 0`
  have hfront : ∀ θ, γ θ ∈ frontier Ω := by
    intro θ
    rw [← him, ← hper.sub_zsmul_eq (toIcoDiv h2pi 0 θ)]
    refine Set.mem_image_of_mem γ ?_
    have := toIcoMod_mem_Ico h2pi 0 θ
    rw [zero_add] at this
    exact ⟨this.1, this.2.le⟩
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
  -- identify the limit
  have hcz : ∀ x : ℂ, c * (p + c⁻¹ * x - p) = x := fun x => by field_simp; ring
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 0, windingNumber γ' ((s : ℂ) * Complex.I) -
      windingNumber γ' (-((s : ℂ) * Complex.I)) = windingNumber γ z₀ := by
    filter_upwards [Ioo_mem_nhdsGT hh] with s hs
    rw [windingNumber_affine γ hc0, windingNumber_affine γ hc0]
    have hin' : p + c⁻¹ * ((s : ℂ) * Complex.I) ∈ Ω := by
      rw [hΩ _ (by rw [hcz]; simpa using hr) (by rw [hcz]; simpa [abs_of_pos hs.1] using hs.2),
        hcz]
      simpa [hf0] using hs.1
    have hout' : p + c⁻¹ * (-((s : ℂ) * Complex.I)) ∉ closure Ω := by
      refine chart_notMem_closure hf hΩ (by rw [hcz]; simpa using hr)
        (by rw [hcz]; simpa [abs_of_pos hs.1] using hs.2) ?_
      rw [hcz]
      simpa [hf0] using hs.1
    rw [hin _ hin', hout _ hout', sub_zero]
  have hσeq : σ' = windingNumber γ z₀ :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (EventuallyEq.symm hev))
  rcases hσ' with h1 | h1
  · exact ⟨1, Or.inl rfl, fun z hz => by rw [hin z hz, ← hσeq, h1]; simp, hout⟩
  · exact ⟨-1, Or.inr rfl, fun z hz => by rw [hin z hz, ← hσeq, h1]; simp, hout⟩

end PolyaNeumann

end
