/-
Adapted from RequestProject/MainBase.lean, lines 1031–1165 and 2170–2862, in
Quanyu Tang and Zuoqin Wang's Apache-2.0 Lean formalization at commit
b70cda58ddc4f4761a5a857b056310e713412386. That project records Aristotle
and Codex assistance. The surrounding unrelated sections were omitted.
-/
module

public import Mathlib

@[expose] public section

noncomputable section

section

/-! ## Injective holomorphic maps have nonvanishing derivative -/

open Complex Metric Filter Topology Set

/-- **Injective holomorphic functions have nonzero derivative.** -/
theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  intro h0
  have hUa : U ∈ 𝓝 a := hU.mem_nhds ha
  have han : AnalyticAt ℂ f a := (hf.analyticOnNhd hU) a ha
  set g : ℂ → ℂ := fun z => f z - f a with hg
  have hgan : AnalyticAt ℂ g a := han.sub analyticAt_const
  -- `g` is not identically zero near `a`
  have hnz : ¬ ∀ᶠ z in 𝓝 a, g z = 0 := by
    intro hev
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hev hUa)
    have hmem : a + (ε / 2 : ℝ) ∈ ball a ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have h1 := hεsub hmem
    have h2 : f (a + (ε / 2 : ℝ)) = f a := sub_eq_zero.1 h1.1
    have := hinj h1.2 ha h2
    have : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination this
    have : ε / 2 = 0 := by exact_mod_cast this
    linarith
  obtain ⟨n, h, hhan, hha, hgeq⟩ := hgan.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnz
  simp only [smul_eq_mul] at hgeq
  -- `n ≥ 2`
  have hga : g a = 0 := by simp [hg]
  have hderg : deriv g a = 0 := by
    have : deriv g a = deriv f a := by
      rw [hg, deriv_sub_const]
    rw [this, h0]
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · exfalso
      interval_cases n
      · have := hgeq.self_of_nhds
        simp only [pow_zero, one_mul] at this
        exact hha (this ▸ hga)
      · have hd : HasDerivAt (fun z => (z - a) ^ 1 * h z)
            (1 * h a + (a - a) ^ 1 * deriv h a) a := by
          have h1 : HasDerivAt (fun z => (z - a) ^ 1) 1 a := by
            simpa using (hasDerivAt_id a).sub_const a
          exact h1.mul hhan.differentiableAt.hasDerivAt
        have := hd.deriv
        rw [← Filter.EventuallyEq.deriv_eq hgeq] at this
        rw [hderg] at this
        simp at this
        exact hha this.symm
    · exact hn
  have hn0 : n ≠ 0 := by omega
  -- an `n`-th root of `h` near `a`
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ n = h a := IsAlgClosed.exists_pow_nat_eq _ (by omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hha (by rw [← hc, zero_pow hn0])
  set q : ℂ → ℂ := fun z => h z / h a with hq
  have hqa : q a = 1 := div_self hha
  have hqan : AnalyticAt ℂ q a := hhan.div analyticAt_const hha
  have hslit : q a ∈ slitPlane := by rw [hqa]; exact one_mem_slitPlane
  set ψ : ℂ → ℂ := fun z => c * exp (log (q z) / n) with hψ
  have hψan : AnalyticAt ℂ ψ a := by
    apply analyticAt_const.mul
    apply AnalyticAt.cexp
    exact (hqan.clog hslit).div analyticAt_const (by exact_mod_cast hn0)
  have hψpow : ∀ᶠ z in 𝓝 a, ψ z ^ n = h z := by
    have hev : ∀ᶠ z in 𝓝 a, q z ∈ slitPlane :=
      hqan.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hslit)
    filter_upwards [hev] with z hz
    have hqz : q z ≠ 0 := slitPlane_ne_zero hz
    rw [hψ, mul_pow, hc, ← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn0),
      exp_log hqz, hq]
    field_simp
  set φ : ℂ → ℂ := fun z => (z - a) * ψ z with hφ
  have hφan : AnalyticAt ℂ φ a := (analyticAt_id.sub analyticAt_const).mul hψan
  have hφa : φ a = 0 := by simp [hφ]
  have hψa : ψ a = c := by simp [hψ, hqa]
  have hφd : HasDerivAt φ c a := by
    have := ((hasDerivAt_id a).sub_const a).mul hψan.differentiableAt.hasDerivAt
    convert this using 1
    · funext z
      rfl
    · simp [hψa]
  have hφnc : ¬ ∀ᶠ z in 𝓝 a, φ z = φ a := by
    intro hev
    have : deriv φ a = 0 := by
      have hev' : φ =ᶠ[𝓝 a] fun _ => φ a := hev
      rw [hev'.deriv_eq]
      simp
    rw [hφd.deriv] at this
    exact hc0 this
  have hopen : 𝓝 (φ a) ≤ map φ (𝓝 a) :=
    hφan.eventually_constant_or_nhds_le_map_nhds.resolve_left hφnc
  -- a neighbourhood of `a` where `g = φⁿ`
  have hVmem : {z | z ∈ U ∧ g z = φ z ^ n} ∈ 𝓝 a := by
    filter_upwards [hUa, hgeq, hψpow] with z hz h1 h2
    refine ⟨hz, ?_⟩
    rw [h1, hφ, mul_pow, h2]
  have himg : φ '' {z | z ∈ U ∧ g z = φ z ^ n} ∈ 𝓝 0 := by
    rw [← hφa]
    exact hopen (image_mem_map hVmem)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 himg
  set ε : ℂ := ((δ / 2 : ℝ) : ℂ) with hε
  set ζ : ℂ := exp (2 * Real.pi * I / n) with hζ
  have hζprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hζ1 : ζ ≠ 1 := hζprim.ne_one (by omega)
  have hζn : ζ ^ n = 1 := hζprim.pow_eq_one
  have hζnorm : ‖ζ‖ = 1 := hζprim.norm'_eq_one hn0
  have hεnorm : ‖ε‖ = δ / 2 := by
    rw [hε, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, norm_zero] at hεnorm; linarith
  have hm1 : ε ∈ ball (0 : ℂ) δ := by
    rw [mem_ball_zero_iff, hεnorm]; linarith
  have hm2 : ε * ζ ∈ ball (0 : ℂ) δ := by
    rw [mem_ball_zero_iff, norm_mul, hεnorm, hζnorm]; linarith
  obtain ⟨z1, ⟨hz1U, hz1g⟩, hz1⟩ := hδsub hm1
  obtain ⟨z2, ⟨hz2U, hz2g⟩, hz2⟩ := hδsub hm2
  have hgz : g z1 = g z2 := by
    rw [hz1g, hz2g, hz1, hz2, mul_pow, hζn, mul_one]
  have hfz : f z1 = f z2 := by
    simpa [hg] using hgz
  have hz12 := hinj hz1U hz2U hfz
  rw [hz12, hz2] at hz1
  have : ε * (ζ - 1) = 0 := by linear_combination hz1
  rcases mul_eq_zero.1 this with h | h
  · exact hε0 h
  · exact hζ1 (sub_eq_zero.1 h)

end

section

/-! ## Disk automorphisms `z ↦ (z - a) / (1 - ā z)` -/

open Complex Metric

/-- The disk automorphism `mob a z = (z - a) / (1 - ā z)`. -/
def mob (a z : ℂ) : ℂ := (z - a) / (1 - (starRingEnd ℂ) a * z)

lemma mob_denom_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * z = 1 := by linear_combination -h
  have : ‖(starRingEnd ℂ) a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := by gcongr
      _ < 1 := by linarith
  rw [h1] at this
  simp at this

/-- The key identity `|1 - ā z|² - |z - a|² = (1 - |a|²)(1 - |z|²)`. -/
lemma normSq_identity (a z : ℂ) :
    normSq (1 - (starRingEnd ℂ) a * z) - normSq (z - a) =
      (1 - normSq a) * (1 - normSq z) := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

lemma norm_mob_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖mob a z‖ < 1 := by
  have hd := mob_denom_ne_zero ha hz
  unfold mob
  rw [norm_div, div_lt_one (norm_pos_iff.2 hd)]
  have hid := normSq_identity a z
  have ha2 : normSq a < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hz2 : normSq z < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have : normSq (z - a) < normSq (1 - (starRingEnd ℂ) a * z) := by
    nlinarith [mul_pos (sub_pos.2 ha2) (sub_pos.2 hz2)]
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]

lemma mob_mem_ball {a z : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    mob a z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at *
  exact norm_mob_lt_one ha hz

@[simp] lemma mob_self (a : ℂ) : mob a a = 0 := by simp [mob]

@[simp] lemma mob_zero (a : ℂ) : mob a 0 = -a := by simp [mob]

lemma mob_neg_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob (-a) (mob a z) = z := by
  have hd := mob_denom_ne_zero ha hz
  have hna : 1 - (starRingEnd ℂ) a * a ≠ 0 := mob_denom_ne_zero ha ha
  unfold mob
  rw [map_neg]
  have h2 : 1 - -(starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) =
      (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) := by
    field_simp; ring
  rw [h2, div_eq_iff (div_ne_zero hna hd)]
  generalize (starRingEnd ℂ) a = c at *
  rw [div_sub' hd, mul_div_assoc', div_left_inj' hd]
  ring

lemma mob_injOn {a : ℂ} (ha : ‖a‖ < 1) : Set.InjOn (mob a) (ball 0 1) := by
  intro z hz w hw h
  rw [mem_ball_zero_iff] at hz hw
  rw [← mob_neg_mob ha hz, ← mob_neg_mob ha hw, h]

lemma hasDerivAt_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (mob a) ((1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2) z := by
  have hd := mob_denom_ne_zero ha hz
  have h1 : HasDerivAt (fun w => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w => 1 - (starRingEnd ℂ) a * w) (-(starRingEnd ℂ) a) z := by
    simpa using ((hasDerivAt_id z).const_mul ((starRingEnd ℂ) a)).const_sub 1
  have := h1.div h2 hd
  change HasDerivAt ((fun w => w - a) / fun w => 1 - (starRingEnd ℂ) a * w)
    ((1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2) z
  convert this using 1
  field_simp
  ring

lemma differentiableAt_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (mob a) z := (hasDerivAt_mob ha hz).differentiableAt

lemma mob_eq_zero_iff {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob a z = 0 ↔ z = a := by
  constructor
  · intro h
    have hd := mob_denom_ne_zero ha hz
    unfold mob at h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hd
  · rintro rfl; simp

end

section

/-! ## Holomorphic square roots on simply connected domains -/

open Complex Metric Filter Topology Set

/-- A continuous square root of a differentiable function is differentiable where it does
not vanish. -/
lemma hasDerivAt_of_sq_eq {g f : ℂ → ℂ} {z : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 z)
    (hg : ContinuousAt g z) (hsq : ∀ w ∈ U, g w ^ 2 = f w) (hf : DifferentiableAt ℂ f z)
    (hgz : g z ≠ 0) : HasDerivAt g (deriv f z / (2 * g z)) z := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hsum : Tendsto (fun w => g w + g z) (𝓝[≠] z) (𝓝 (2 * g z)) := by
    have : Tendsto (fun w => g w + g z) (𝓝 z) (𝓝 (g z + g z)) := hg.add tendsto_const_nhds
    rw [two_mul]
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : (2 * g z) ≠ 0 := mul_ne_zero two_ne_zero hgz
  have hlim := hf.hasDerivAt.tendsto_slope.div hsum h2
  refine hlim.congr' ?_
  have hev1 : ∀ᶠ w in 𝓝[≠] z, g w + g z ≠ 0 := hsum.eventually_ne h2
  have hev2 : ∀ᶠ w in 𝓝[≠] z, w ∈ U := nhdsWithin_le_nhds hU
  filter_upwards [hev1, hev2, self_mem_nhdsWithin] with w hw1 hw2 hw3
  have hzU : z ∈ U := mem_of_mem_nhds hU
  rw [Pi.div_apply, slope_def_field, slope_def_field, ← hsq w hw2, ← hsq z hzU]
  have hwz : w - z ≠ 0 := sub_ne_zero.2 hw3
  field_simp
  ring

open Classical in
/-- **Holomorphic square roots.** A nonvanishing holomorphic function on a simply connected
open subset of `ℂ` has a holomorphic square root. -/
theorem exists_sqrt_of_simplyConnected {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ Ω, g z ^ 2 = f z := by
  haveI := hΩ.locPathConnectedSpace
  obtain ⟨z0⟩ : Nonempty Ω := inferInstance
  have hp := isCoveringMap_npow (𝕜 := ℂ) 2 (by norm_num)
  let F : C(Ω, {x : ℂ // x ≠ 0}) :=
    ⟨fun z => ⟨f z, hf0 z z.2⟩, by
      refine Continuous.subtype_mk ?_ _
      exact hf.continuousOn.restrict⟩
  obtain ⟨e0, he0⟩ : ∃ e : ℂ, e ^ 2 = f z0 := IsAlgClosed.exists_pow_nat_eq _ two_pos
  have he0' : e0 ≠ 0 := by
    rintro rfl
    exact hf0 z0 z0.2 (by simpa using he0.symm)
  obtain ⟨G, ⟨-, hGp⟩, -⟩ :=
    hp.existsUnique_continuousMap_lifts F z0 ⟨e0, he0'⟩ (Subtype.ext he0)
  set g : ℂ → ℂ := fun z => if h : z ∈ Ω then ((G ⟨z, h⟩ : {x : ℂ // x ≠ 0}) : ℂ) else 0
    with hg_def
  have hsq : ∀ z ∈ Ω, g z ^ 2 = f z := by
    intro z hz
    have := congrArg Subtype.val (congrFun hGp ⟨z, hz⟩)
    simpa [hg_def, hz, F] using this
  have hne : ∀ z ∈ Ω, g z ≠ 0 := by
    intro z hz
    simp only [hg_def, hz, dite_true]
    exact (G ⟨z, hz⟩).2
  have hcont : ContinuousOn g Ω := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : Ω.domRestrict g = fun z : Ω => ((G z : {x : ℂ // x ≠ 0}) : ℂ) := by
      funext z
      simp [hg_def, z.2]
    rw [this]
    exact continuous_subtype_val.comp G.continuous
  refine ⟨g, ?_, hsq⟩
  intro z hz
  have hU : Ω ∈ 𝓝 z := hΩ.mem_nhds hz
  exact (hasDerivAt_of_sq_eq hU (hcont.continuousAt hU) hsq
    (hf.differentiableAt hU) (hne z hz)).differentiableAt.differentiableWithinAt

end

section

/-! ## Montel's theorem -/

open Complex Metric Filter Topology Set

/-- Cauchy estimate: a holomorphic family bounded by `1` on `U` is equicontinuous at every
point of `U`. -/
lemma equicontinuousAt_of_norm_le_one {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hb : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ 1) {z : ℂ}
    (hz : z ∈ U) : EquicontinuousAt F z := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  set r := ε / 3 with hr
  have hr0 : 0 < r := by positivity
  have hsub : ∀ y ∈ ball z r, closedBall y r ⊆ U := by
    intro y hy w hw
    apply hεU
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hw
    calc dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
      _ < r + r := by linarith
      _ < ε := by rw [hr]; linarith
  have hderiv : ∀ i, ∀ y ∈ ball z r, ‖deriv (F i) y‖ ≤ 1 / r := by
    intro i y hy
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hr0
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball y hr0.ne']
      exact (hF i).mono (hsub y hy)
    · intro w hw
      exact hb i w (hsub y hy (sphere_subset_closedBall hw))
  have hdiff : ∀ i, ∀ y ∈ ball z r, DifferentiableAt ℂ (F i) y := by
    intro i y hy
    exact (hF i).differentiableAt (hU.mem_nhds (hsub y hy (mem_closedBall_self hr0.le)))
  have hlip : ∀ i, ∀ y ∈ ball z r, ‖F i y - F i z‖ ≤ 1 / r * ‖y - z‖ := fun i y hy =>
    (convex_ball z r).norm_image_sub_le_of_norm_deriv_le (hdiff i) (hderiv i)
      (mem_ball_self hr0) hy
  rw [Metric.equicontinuousAt_iff]
  intro e he
  refine ⟨min r (e * r / 2), by positivity, fun y hy i => ?_⟩
  have hy1 : y ∈ ball z r := mem_ball.2 (lt_of_lt_of_le hy (min_le_left _ _))
  have hy2 : dist y z < e * r / 2 := lt_of_lt_of_le hy (min_le_right _ _)
  rw [dist_comm, dist_eq_norm]
  calc ‖F i y - F i z‖ ≤ 1 / r * ‖y - z‖ := hlip i y hy1
    _ ≤ 1 / r * (e * r / 2) := by
        gcongr; rw [← dist_eq_norm]; exact hy2.le
    _ = e / 2 := by field_simp
    _ < e := by linarith

/-- **Montel's theorem.** A family of holomorphic functions on an open set `U`, bounded by `1`
on `U`, converges locally uniformly on `U` along any ultrafilter. -/
theorem montel {ι : Type*} (l : Ultrafilter ι) {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hb : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ 1) :
    ∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f (l : Filter ι) U := by
  have hpt : ∀ z, ∃ w, z ∈ U → Tendsto (fun i => F i z) (l : Filter ι) (𝓝 w) := by
    intro z
    by_cases hz : z ∈ U
    · obtain ⟨w, -, hw⟩ := (isCompact_closedBall (0 : ℂ) 1).ultrafilter_le_nhds
        (l.map (fun i => F i z)) (by
          rw [Ultrafilter.coe_map]
          refine tendsto_principal.2 (Eventually.of_forall fun i => ?_)
          rw [mem_closedBall_zero_iff]; exact hb i z hz)
      exact ⟨w, fun _ => by rwa [Ultrafilter.coe_map] at hw⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose f hf using hpt
  refine ⟨f, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  have heq : ∀ K' ∈ ({K} : Set (Set ℂ)), EquicontinuousOn F K' := by
    rintro K' rfl x hx
    exact (equicontinuousAt_of_norm_le_one hU hF hb (hKU hx)).equicontinuousWithinAt _
  have key := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' (𝔖 := {K})
    (by simpa using hK) heq (l : Filter ι) f).2 (by
      rw [tendsto_pi_nhds]
      rintro ⟨x, hx⟩
      simp only [sUnion_singleton] at hx
      exact hf x (hKU hx))
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at key
  exact key K rfl

end

section

/-! ## Hurwitz's theorem -/

open Complex Metric Filter Topology Set

/-- Local Hurwitz theorem for nonvanishing functions. -/
theorem hurwitz_ne_zero {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hF : ∀ i, DifferentiableOn ℂ (F i) (closedBall a r))
    (hF0 : ∀ i, ∀ z ∈ closedBall a r, F i z ≠ 0)
    (hconv : TendstoUniformlyOn F g l (closedBall a r))
    (hg : ContinuousOn g (sphere a r)) (hg0 : ∀ z ∈ sphere a r, g z ≠ 0) : g a ≠ 0 := by
  obtain ⟨z1, hz1, hmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr.le) hg.norm
  set m := ‖g z1‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (hg0 z1 hz1)
  rw [Metric.tendstoUniformlyOn_iff] at hconv
  obtain ⟨i, hi⟩ := (hconv (m / 2) (by positivity)).exists
  have hbd : ∀ z ∈ sphere a r, ‖(F i z)⁻¹‖ ≤ 2 / m := by
    intro z hz
    have h1 : m ≤ ‖g z‖ := hmin hz
    have h2 : ‖g z - F i z‖ < m / 2 := by
      rw [← dist_eq_norm]; exact hi z (sphere_subset_closedBall hz)
    have h3 : m / 2 ≤ ‖F i z‖ := by
      have := norm_sub_norm_le (g z) (g z - F i z)
      simp only [sub_sub_cancel] at this
      linarith
    rw [norm_inv]
    calc ‖F i z‖⁻¹ ≤ (m / 2)⁻¹ := inv_anti₀ (by positivity) h3
      _ = 2 / m := by rw [inv_div]
  have hd : DiffContOnCl ℂ (fun z => (F i z)⁻¹) (ball a r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball a hr.ne']
    exact (hF i).inv (hF0 i)
  have hFa : ‖(F i a)⁻¹‖ ≤ 2 / m :=
    norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
      (by rw [frontier_ball a hr.ne']; exact hbd) (subset_closure (mem_ball_self hr))
  have hFa' : m / 2 ≤ ‖F i a‖ := by
    have hne : F i a ≠ 0 := hF0 i a (mem_closedBall_self hr.le)
    rw [norm_inv] at hFa
    have hpos : 0 < ‖F i a‖ := norm_pos_iff.2 hne
    rw [inv_le_comm₀ hpos (by positivity), inv_div] at hFa
    exact hFa
  have hga : ‖g a - F i a‖ < m / 2 := by
    rw [← dist_eq_norm]; exact hi a (mem_closedBall_self hr.le)
  intro h0
  rw [h0, zero_sub, norm_neg] at hga
  linarith

/-- **Hurwitz's theorem.** A locally uniform limit of injective holomorphic functions on a
connected open set, whose derivative does not vanish at some point, is injective. -/
theorem hurwitz_injOn {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hinj : ∀ i, InjOn (F i) U)
    (hconv : TendstoLocallyUniformlyOn F f l U) {z0 : ℂ} (hz0 : z0 ∈ U)
    (hd : deriv f z0 ≠ 0) : InjOn f U := by
  intro a ha b hb hab
  by_contra hne
  have hfd : DifferentiableOn ℂ f U :=
    hconv.differentiableOn (Eventually.of_forall hF) hU
  have han : AnalyticOnNhd ℂ f U := hfd.analyticOnNhd hU
  set g : ℂ → ℂ := fun z => f z - f b with hg
  have hgan : AnalyticOnNhd ℂ g U := fun z hz => (han z hz).sub analyticAt_const
  have hnz : ¬ ∀ᶠ z in 𝓝 a, g z = 0 := by
    intro hev
    have hEq : EqOn g 0 U := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc ha hev
    have hloc : f =ᶠ[𝓝 z0] fun _ => f b := by
      filter_upwards [hU.mem_nhds hz0] with z hz
      have := hEq hz
      simp only [hg, Pi.zero_apply, sub_eq_zero] at this
      exact this
    apply hd
    rw [hloc.deriv_eq]
    simp
  have hev : ∀ᶠ z in 𝓝[≠] a, g z ≠ 0 :=
    ((hgan a ha).eventually_eq_zero_or_eventually_ne_zero).resolve_left hnz
  rw [eventually_nhdsWithin_iff] at hev
  have hbU : ({b}ᶜ : Set ℂ) ∈ 𝓝 a := isOpen_compl_singleton.mem_nhds hne
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1
    (inter_mem (inter_mem hev (hU.mem_nhds ha)) hbU)
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcb : closedBall a r ⊆ ball a ε := closedBall_subset_ball (by rw [hr]; linarith)
  have hcbU : closedBall a r ⊆ U := fun z hz => (hεsub (hcb hz)).1.2
  have hcbb : ∀ z ∈ closedBall a r, z ≠ b := fun z hz => (hεsub (hcb hz)).2
  have hcbg : ∀ z ∈ closedBall a r, z ≠ a → g z ≠ 0 := fun z hz => (hεsub (hcb hz)).1.1
  have hunif : TendstoUniformlyOn F f l (closedBall a r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hcbU (isCompact_closedBall a r)
  have hptb : Tendsto (fun i => F i b) l (𝓝 (f b)) := hconv.tendsto_at hb
  have hconv' : TendstoUniformlyOn (fun i z => F i z - F i b) g l (closedBall a r) :=
    hunif.sub (hptb.tendstoUniformlyOn_const _)
  have key := hurwitz_ne_zero hr0 (F := fun i z => F i z - F i b) (g := g)
    (fun i => ((hF i).mono hcbU).sub_const _)
    (fun i z hz h => hcbb z hz (hinj i (hcbU hz) hb (sub_eq_zero.1 h)))
    hconv' ((hfd.mono hcbU).continuousOn.sub continuousOn_const |>.mono
      sphere_subset_closedBall)
    (fun z hz => hcbg z (sphere_subset_closedBall hz) (by
      rintro rfl
      rw [mem_sphere, dist_self] at hz
      exact hr0.ne hz))
  exact key (by simp [hg, hab])

end

section

/-! ## The Riemann mapping theorem -/

open Complex Metric Filter Topology Set

/-- Open mapping theorem for injective holomorphic maps on a connected open set. -/
lemma isOpen_image_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {s : Set ℂ} (hs : s ⊆ U)
    (hso : IsOpen s) : IsOpen (f '' s) := by
  rcases (hf.analyticOnNhd hU).is_constant_or_isOpen hUc with ⟨w, hw⟩ | h
  · rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · simp
    · exfalso
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z (hs hz)
      have hmem : z + (ε / 2 : ℝ) ∈ ball z ε := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        linarith
      have := hinj (hεU hmem) (hs hz) ((hw _ (hεU hmem)).trans (hw z (hs hz)).symm)
      have : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination this
      have : ε / 2 = 0 := by exact_mod_cast this
      linarith
  · exact h s hs hso

/-- The admissible family: injective holomorphic maps `Ω → 𝔻` sending `z₀` to `0`. -/
def Admissible (Ω : Set ℂ) (z₀ : ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f Ω ∧ InjOn f Ω ∧ MapsTo f Ω (ball 0 1) ∧ f z₀ = 0

/-- The admissible family is nonempty (square-root trick). -/
lemma exists_admissible {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) : ∃ f, Admissible Ω z₀ f := by
  have hUc : IsPreconnected Ω := isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨a, ha⟩ : ∃ a, a ∉ Ω := by
    by_contra h; push_neg at h; exact hne (eq_univ_of_forall h)
  have hza : ∀ z ∈ Ω, z - a ≠ 0 := fun z hz h => ha (sub_eq_zero.1 h ▸ hz)
  obtain ⟨g, hgd, hgsq⟩ := exists_sqrt_of_simplyConnected hΩ
    (f := fun z => z - a) (differentiableOn_id.sub_const a) hza
  have hginj : InjOn g Ω := by
    intro z hz w hw h
    have := hgsq z hz
    rw [h, hgsq w hw] at this
    linear_combination -this
  have hgneg : ∀ z ∈ Ω, ∀ w ∈ Ω, g z ≠ -g w := by
    intro z hz w hw h
    have h1 := hgsq z hz
    rw [h, neg_sq, hgsq w hw] at h1
    have hzw : w = z := by linear_combination h1
    subst hzw
    have : g w = 0 := by linear_combination h / 2
    exact hza w hw (by rw [← hgsq w hw, this]; ring)
  have hopen : IsOpen (g '' Ω) := isOpen_image_of_injOn hΩ hUc hgd hginj subset_rfl hΩ
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hopen (g z₀) ⟨z₀, hz₀, rfl⟩
  have hfar : ∀ z ∈ Ω, ρ ≤ ‖g z + g z₀‖ := by
    intro z hz
    by_contra hlt
    push_neg at hlt
    have : -g z ∈ ball (g z₀) ρ := by
      rw [mem_ball, dist_eq_norm, ← norm_neg]
      convert hlt using 2; ring
    obtain ⟨w, hw, hgw⟩ := hρsub this
    exact hgneg w hw z hz hgw
  have hne0 : ∀ z ∈ Ω, g z + g z₀ ≠ 0 := fun z hz h => by
    have := hfar z hz; rw [h, norm_zero] at this; linarith
  have hinvle : ∀ z ∈ Ω, ‖(g z + g z₀)⁻¹‖ ≤ 1 / ρ := by
    intro z hz
    rw [norm_inv, one_div]
    exact inv_anti₀ hρ (hfar z hz)
  refine ⟨fun z => ((ρ / 4 : ℝ) : ℂ) * ((g z + g z₀)⁻¹ - (g z₀ + g z₀)⁻¹), ?_, ?_, ?_, ?_⟩
  · intro z hz
    apply DifferentiableWithinAt.const_mul
    apply DifferentiableWithinAt.sub_const
    exact ((hgd z hz).add_const _).inv (hne0 z hz)
  · intro z hz w hw h
    simp only at h
    have hρ4 : ((ρ / 4 : ℝ) : ℂ) ≠ 0 := by
      have : ρ / 4 ≠ 0 := by positivity
      exact_mod_cast this
    have h1 := mul_left_cancel₀ hρ4 h
    have h2 : (g z + g z₀)⁻¹ = (g w + g z₀)⁻¹ := by linear_combination h1
    rw [inv_inj] at h2
    exact hginj hz hw (by linear_combination h2)
  · intro z hz
    rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ρ / 4 * ‖(g z + g z₀)⁻¹ - (g z₀ + g z₀)⁻¹‖
        ≤ ρ / 4 * (‖(g z + g z₀)⁻¹‖ + ‖(g z₀ + g z₀)⁻¹‖) := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ρ / 4 * (1 / ρ + 1 / ρ) := by
          gcongr
          · exact hinvle z hz
          · exact hinvle z₀ hz₀
      _ = 1 / 2 := by field_simp; ring
      _ < 1 := by norm_num
  · simp

/-- Cauchy estimate for admissible maps. -/
lemma norm_deriv_le_of_admissible {Ω : Set ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall z₀ r ⊆ Ω) {f : ℂ → ℂ} (hf : Admissible Ω z₀ f) :
    ‖deriv f z₀‖ ≤ 1 / r := by
  apply norm_deriv_le_of_forall_mem_sphere_norm_le hr
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr.ne']
    exact hf.1.mono hsub
  · intro w hw
    exact (mem_ball_zero_iff.1 (hf.2.2.1 (hsub (sphere_subset_closedBall hw)))).le

/-- Existence of an extremal admissible map (Montel + Hurwitz). -/
lemma exists_extremal {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ f, Admissible Ω z₀ f ∧ ∀ g, Admissible Ω z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖ := by
  have hUc : IsPreconnected Ω := isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨r, hr, hrsub⟩ : ∃ r > 0, closedBall z₀ r ⊆ Ω := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεsub⟩
  set S : Set ℝ := {t | ∃ g, Admissible Ω z₀ g ∧ ‖deriv g z₀‖ = t} with hS
  obtain ⟨f₁, hf₁⟩ := exists_admissible hΩ hne hz₀
  have hSne : S.Nonempty := ⟨_, f₁, hf₁, rfl⟩
  have hSbdd : BddAbove S := ⟨1 / r, by
    rintro t ⟨g, hg, rfl⟩
    exact norm_deriv_le_of_admissible hr hrsub hg⟩
  have hMpos : 0 < sSup S := by
    have h1 : ‖deriv f₁ z₀‖ ≤ sSup S := le_csSup hSbdd ⟨f₁, hf₁, rfl⟩
    have h2 : 0 < ‖deriv f₁ z₀‖ :=
      norm_pos_iff.2 (deriv_ne_zero_of_injOn hΩ hf₁.1 hf₁.2.1 hz₀)
    linarith
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hSne hSbdd
  choose F hF hFu using huS
  set l : Ultrafilter ℕ := Ultrafilter.of atTop
  have hl : (l : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨f, hconv⟩ := montel l hΩ (fun n => (hF n).1)
    (fun n z hz => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le)
  have hfd : DifferentiableOn ℂ f Ω :=
    hconv.differentiableOn (Eventually.of_forall fun n => (hF n).1) hΩ
  have hderiv : Tendsto (fun n => deriv (F n) z₀) (l : Filter ℕ) (𝓝 (deriv f z₀)) :=
    (hconv.deriv (Eventually.of_forall fun n => (hF n).1) hΩ).tendsto_at hz₀
  have hnorm : ‖deriv f z₀‖ = sSup S := by
    have h1 : Tendsto (fun n => ‖deriv (F n) z₀‖) (l : Filter ℕ) (𝓝 ‖deriv f z₀‖) :=
      hderiv.norm
    have h2 : Tendsto (fun n => ‖deriv (F n) z₀‖) (l : Filter ℕ) (𝓝 (sSup S)) := by
      simp_rw [hFu]; exact hu.mono_left hl
    exact tendsto_nhds_unique h1 h2
  have hd0 : deriv f z₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; linarith
  have hfinj : InjOn f Ω :=
    hurwitz_injOn hΩ hUc (fun n => (hF n).1) (fun n => (hF n).2.1) hconv hz₀ hd0
  have hfz₀ : f z₀ = 0 := by
    have h1 : Tendsto (fun n => F n z₀) (l : Filter ℕ) (𝓝 (f z₀)) := hconv.tendsto_at hz₀
    have h2 : Tendsto (fun n => F n z₀) (l : Filter ℕ) (𝓝 0) := by
      simp_rw [(hF _).2.2.2]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hfle : ∀ z ∈ Ω, ‖f z‖ ≤ 1 := by
    intro z hz
    have h1 : Tendsto (fun n => ‖F n z‖) (l : Filter ℕ) (𝓝 ‖f z‖) :=
      (hconv.tendsto_at hz).norm
    exact le_of_tendsto' h1 fun n => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le
  have hmaps : MapsTo f Ω (ball 0 1) := by
    have hopen : IsOpen (f '' Ω) := isOpen_image_of_injOn hΩ hUc hfd hfinj subset_rfl hΩ
    have hsub : f '' Ω ⊆ closedBall 0 1 := by
      rintro _ ⟨z, hz, rfl⟩; exact mem_closedBall_zero_iff.2 (hfle z hz)
    have := hopen.subset_interior_iff.2 hsub
    rw [interior_closedBall (0 : ℂ) one_ne_zero] at this
    exact fun z hz => this ⟨z, hz, rfl⟩
  refine ⟨f, ⟨hfd, hfinj, hmaps, hfz₀⟩, fun g hg => ?_⟩
  rw [hnorm]
  exact le_csSup hSbdd ⟨g, hg, rfl⟩

/-- The derivative at `0` of `ζ ↦ mob (-w) ((mob (-c) ζ)²)` when `w = -c²`. -/
lemma hasDerivAt_psi {c : ℂ} (hc : ‖c‖ < 1) :
    HasDerivAt (fun ζ => mob (-(-c ^ 2)) (mob (-c) ζ ^ 2))
      (2 * c / (1 + (starRingEnd ℂ) c * c)) 0 := by
  have hc' : ‖-c‖ < 1 := by rwa [norm_neg]
  have hw : ‖-(-c ^ 2)‖ < 1 := by
    rw [neg_neg, norm_pow]; nlinarith [norm_nonneg c]
  have hc2 : ‖c ^ 2‖ < 1 := by rwa [neg_neg] at hw
  have h1 := hasDerivAt_mob hc' (z := 0) (by simp)
  have h2 : HasDerivAt (fun ζ => ζ ^ 2) (2 * mob (-c) 0) (mob (-c) 0) := by
    simpa using hasDerivAt_pow 2 (mob (-c) 0)
  have h3 := hasDerivAt_mob hw (z := mob (-c) 0 ^ 2) (by simpa using hc2)
  have := h3.comp (0 : ℂ) (h2.comp (0 : ℂ) h1)
  convert this using 1
  · funext ζ
    rfl
  simp only [mob_zero, neg_neg, map_neg, map_pow, mul_zero, sub_zero]
  have hden : 1 + (starRingEnd ℂ) c * c ≠ 0 := by
    rw [conj_mul']
    have : (0 : ℝ) ≤ ‖c‖ ^ 2 := by positivity
    intro h
    have h' : ((1 + ‖c‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have : (1 + ‖c‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h'
    linarith
  have hden2 : 1 - (starRingEnd ℂ) c * c ≠ 0 := by
    have := mob_denom_ne_zero hc hc
    exact this
  have hden3 : 1 - (starRingEnd ℂ) c ^ 2 * c ^ 2 ≠ 0 := by
    have : 1 - (starRingEnd ℂ) c ^ 2 * c ^ 2 =
        (1 - (starRingEnd ℂ) c * c) * (1 + (starRingEnd ℂ) c * c) := by ring
    rw [this]; exact mul_ne_zero hden2 hden
  have hden4 : 1 - -(starRingEnd ℂ) c ^ 2 * -c ^ 2 ≠ 0 := by
    have : 1 - -(starRingEnd ℂ) c ^ 2 * -c ^ 2 = 1 - (starRingEnd ℂ) c ^ 2 * c ^ 2 := by ring
    rw [this]; exact hden3
  generalize (starRingEnd ℂ) c = d at *
  have hden' : 1 + c * d ≠ 0 := by rwa [mul_comm]
  have hden3' : 1 - c ^ 2 * d ^ 2 ≠ 0 := by rwa [mul_comm]
  have hfac : 1 - c ^ 2 * d ^ 2 = (1 - d * c) * (1 + c * d) := by ring
  field_simp [hden, hden3]
  ring

/-- `|2c / (1 + |c|²)| < 1` for `|c| < 1`. -/
lemma norm_psi_deriv_lt_one {c : ℂ} (hc : ‖c‖ < 1) :
    ‖2 * c / (1 + (starRingEnd ℂ) c * c)‖ < 1 := by
  rw [conj_mul']
  have h1 : (1 + (‖c‖ : ℂ) ^ 2) = ((1 + ‖c‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_lt_one (by positivity)]
  simp only [norm_ofNat]
  nlinarith [sq_nonneg (1 - ‖c‖), norm_nonneg c]

/-- An extremal admissible map is onto the unit disk. -/
lemma surjOn_of_extremal {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω] {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) {f : ℂ → ℂ} (hf : Admissible Ω z₀ f)
    (hmax : ∀ g, Admissible Ω z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖) :
    SurjOn f Ω (ball 0 1) := by
  intro w hw
  by_contra hnot
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  obtain ⟨hfd, hfinj, hfmaps, hfz₀⟩ := hf
  have hfn : ∀ z ∈ Ω, ‖f z‖ < 1 := fun z hz => mem_ball_zero_iff.1 (hfmaps hz)
  -- `h = mob w ∘ f` does not vanish
  set h : ℂ → ℂ := fun z => mob w (f z) with hh
  have hhd : DifferentiableOn ℂ h Ω := fun z hz =>
    (differentiableAt_mob hw1 (hfn z hz)).comp_differentiableWithinAt z (hfd z hz)
  have hh0 : ∀ z ∈ Ω, h z ≠ 0 := by
    intro z hz h0
    rw [hh, mob_eq_zero_iff hw1 (hfn z hz)] at h0
    exact hnot ⟨z, hz, h0⟩
  obtain ⟨s, hsd, hssq⟩ := exists_sqrt_of_simplyConnected hΩ hhd hh0
  have hsn : ∀ z ∈ Ω, ‖s z‖ < 1 := by
    intro z hz
    have h1 : ‖s z‖ ^ 2 < 1 := by
      rw [← norm_pow, hssq z hz]; exact norm_mob_lt_one hw1 (hfn z hz)
    nlinarith [norm_nonneg (s z)]
  have hsinj : InjOn s Ω := by
    intro z hz z' hz' hzz
    have : h z = h z' := by rw [← hssq z hz, ← hssq z' hz', hzz]
    exact hfinj hz hz' (mob_injOn hw1 (mem_ball_zero_iff.2 (hfn z hz))
      (mem_ball_zero_iff.2 (hfn z' hz')) this)
  set c := s z₀ with hc
  have hcn : ‖c‖ < 1 := hsn z₀ hz₀
  have hc2 : c ^ 2 = -w := by
    rw [hc, hssq z₀ hz₀, hh]; simp [hfz₀]
  have hwc : w = -c ^ 2 := by rw [hc2, neg_neg]
  -- the competitor `F = mob c ∘ s`
  set F : ℂ → ℂ := fun z => mob c (s z) with hF
  have hFadm : Admissible Ω z₀ F := by
    refine ⟨fun z hz => (differentiableAt_mob hcn (hsn z hz)).comp_differentiableWithinAt z
      (hsd z hz), ?_, fun z hz => mob_mem_ball (mem_ball_zero_iff.2 hcn)
      (mem_ball_zero_iff.2 (hsn z hz)), by simp [hF, hc]⟩
    intro z hz z' hz' hzz
    exact hsinj hz hz' (mob_injOn hcn (mem_ball_zero_iff.2 (hsn z hz))
      (mem_ball_zero_iff.2 (hsn z' hz')) hzz)
  -- `f = Ψ ∘ F` on `Ω`
  set Ψ : ℂ → ℂ := fun ζ => mob (-(-c ^ 2)) (mob (-c) ζ ^ 2) with hΨ
  have hfΨ : ∀ z ∈ Ω, f z = Ψ (F z) := by
    intro z hz
    simp only [hΨ, hF]
    rw [mob_neg_mob hcn (hsn z hz), hssq z hz, hh, ← hwc, mob_neg_mob hw1 (hfn z hz)]
  have hFd : HasDerivAt F (deriv F z₀) z₀ :=
    (hFadm.1.differentiableAt (hΩ.mem_nhds hz₀)).hasDerivAt
  have hΨd := hasDerivAt_psi hcn
  have hFz₀ : F z₀ = 0 := hFadm.2.2.2
  rw [← hFz₀] at hΨd
  have hcomp : HasDerivAt (Ψ ∘ F) (2 * c / (1 + (starRingEnd ℂ) c * c) * deriv F z₀) z₀ :=
    hΨd.comp z₀ hFd
  have hfeq : f =ᶠ[𝓝 z₀] Ψ ∘ F := by
    filter_upwards [hΩ.mem_nhds hz₀] with z hz using hfΨ z hz
  have hdf : deriv f z₀ = 2 * c / (1 + (starRingEnd ℂ) c * c) * deriv F z₀ := by
    rw [hfeq.deriv_eq, hcomp.deriv]
  have hfd0 : deriv f z₀ ≠ 0 := deriv_ne_zero_of_injOn hΩ hfd hfinj hz₀
  have hFd0 : deriv F z₀ ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdf; exact hfd0 hdf
  have hlt : ‖deriv f z₀‖ < ‖deriv F z₀‖ := by
    rw [hdf, norm_mul]
    have := norm_psi_deriv_lt_one hcn
    have hpos : 0 < ‖deriv F z₀‖ := norm_pos_iff.2 hFd0
    nlinarith
  have := hmax F hFadm
  linarith

/-- Inverse of a bijective holomorphic map onto the disk. -/
lemma exists_inverse {Ω : Set ℂ} (hΩ : IsOpen Ω) (hUc : IsPreconnected Ω) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f Ω) (hfinj : InjOn f Ω) (hmaps : MapsTo f Ω (ball 0 1))
    (hsurj : SurjOn f Ω (ball 0 1)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 1) ∧ InjOn G (ball 0 1) ∧
      G '' ball 0 1 = Ω := by
  classical
  set G := Function.invFunOn f Ω with hG
  have hGmem : ∀ w ∈ ball (0 : ℂ) 1, G w ∈ Ω ∧ f (G w) = w := fun w hw =>
    Function.invFunOn_pos (hsurj hw)
  have hGf : ∀ z ∈ Ω, G (f z) = z := fun z hz =>
    hfinj (hGmem _ (hmaps hz)).1 hz (hGmem _ (hmaps hz)).2
  refine ⟨G, ?_, ?_, ?_⟩
  · intro w hw
    have hwn : ball (0 : ℂ) 1 ∈ 𝓝 w := isOpen_ball.mem_nhds hw
    obtain ⟨hGw, hfGw⟩ := hGmem w hw
    have hcont : ContinuousAt G w := by
      rw [ContinuousAt, (nhds_basis_opens (G w)).tendsto_right_iff]
      rintro V ⟨hV, hVo⟩
      have hopen : IsOpen (f '' (V ∩ Ω)) :=
        isOpen_image_of_injOn hΩ hUc hfd hfinj inter_subset_right (hVo.inter hΩ)
      have hmem : w ∈ f '' (V ∩ Ω) := ⟨G w, ⟨hV, hGw⟩, hfGw⟩
      filter_upwards [hopen.mem_nhds hmem] with y hy
      obtain ⟨z, ⟨hzV, hzΩ⟩, rfl⟩ := hy
      rw [hGf z hzΩ]; exact hzV
    have hfder : HasDerivAt f (deriv f (G w)) (G w) :=
      (hfd.differentiableAt (hΩ.mem_nhds hGw)).hasDerivAt
    have hne := deriv_ne_zero_of_injOn hΩ hfd hfinj hGw
    have hev : ∀ᶠ y in 𝓝 w, f (G y) = y := by
      filter_upwards [hwn] with y hy using (hGmem y hy).2
    exact (hfder.of_local_left_inverse hcont hne hev).differentiableAt.differentiableWithinAt
  · intro w hw w' hw' h
    rw [← (hGmem w hw).2, ← (hGmem w' hw').2, h]
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact (hGmem w hw).1
    · intro hz; exact ⟨f z, hmaps hz, hGf z hz⟩

/-- **Riemann mapping theorem.** Every simply connected open subset `Ω ≠ ℂ` of the plane is
the image of the open unit disk under an injective holomorphic map. (Simple connectivity
includes nonemptiness.) -/
theorem riemann_mapping_theorem (Ω : Set ℂ) (hopen : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 1) ∧ InjOn G (ball 0 1) ∧
      G '' ball 0 1 = Ω := by
  have hUc : IsPreconnected Ω := isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨⟨z₀, hz₀⟩⟩ : Nonempty Ω := inferInstance
  obtain ⟨f, hf, hmax⟩ := exists_extremal hopen hne hz₀
  exact exists_inverse hopen hUc hf.1 hf.2.1 hf.2.2.1 (surjOn_of_extremal hopen hz₀ hf hmax)

end

end
