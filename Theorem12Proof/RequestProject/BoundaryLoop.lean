module

public import Theorem12Proof.RequestProject.BoundaryWalk

/-!
# The boundary walk closes up into a Lipschitz Jordan curve

For a bounded Lipschitz domain, the boundary walk (`walk`) eventually revisits a point
(`WalkData.exists_pair`, by compactness of `∂Ω`), hence returns to its starting point
(`WalkData.exists_return`, by backward uniqueness of the walk, which comes from consistency of
orientation). Stopping at the first return gives a closed Lipschitz curve, injective before the
return (`WalkData.exists_loop`), whose image is open and closed in `∂Ω`
(`WalkData.image_eq`). Hence, when `∂Ω` is connected, it is a single Lipschitz Jordan curve
(`exists_jordanParam_of_isPreconnected_frontier`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

lemma IsChartAt.center_mem_box {Ω : Set ℂ} {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) : p ∈ chartBox p c r h := by
  simp [chartBox, hch.2.1, hch.2.2.1]

section Loop

variable {Ω : Set ℂ} {ρ H : ℝ} {K : NNReal} {ch : ℂ → ℂ × (ℝ → ℝ)} {ℓ : ℝ} {p₀ : ℂ}

lemma WalkData.ρ_pos (hw : WalkData Ω ρ H K ch ℓ p₀) : 0 < ρ := hw.ℓ_pos.trans hw.ℓ_lt

/-- The walk stays in an open box for nearby times. -/
lemma WalkData.eventually_box (hw : WalkData Ω ρ H K ch ℓ p₀) {s : ℝ} {p c : ℂ} {r h : ℝ}
    (hbox : walk ch ℓ p₀ s ∈ chartBox p c r h) :
    ∃ ε > 0, ∀ s' ∈ Icc (s - ε) (s + ε), walk ch ℓ p₀ s' ∈ chartBox p c r h := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
    ((isOpen_chartBox p c r h).preimage hw.continuous_walk) s hbox
  refine ⟨δ / 2, by positivity, fun s' hs' => hball ?_⟩
  rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hs'.1, hs'.2]

/-- The walk is locally injective. -/
lemma WalkData.locally_injective (hw : WalkData Ω ρ H K ch ℓ p₀) {s : ℝ} (hs : 0 ≤ s) :
    ∃ ε > 0, InjOn (walk ch ℓ p₀) (Icc (s - ε) (s + ε)) := by
  have hP := hw.walk_mem_frontier (t := s) (by linarith [hw.ρ_pos])
  have hch := hw.chart _ hP
  obtain ⟨ε, hε, hmono⟩ := hw.walk_local_strictMono hs hch hch.center_mem_box
  refine ⟨ε, hε, fun a ha b hb hab => hmono.injOn ha hb ?_⟩
  simp only [walkX, hab]

/-- **Return to the start.** If the walk revisits a point, it returns to its starting point. -/
theorem WalkData.exists_return (hw : WalkData Ω ρ H K ch ℓ p₀) {s₀ t₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hst : s₀ < t₀) (heq : walk ch ℓ p₀ s₀ = walk ch ℓ p₀ t₀) :
    ∃ T, 0 < T ∧ T ≤ t₀ ∧ walk ch ℓ p₀ T = walk ch ℓ p₀ 0 := by
  have hρ := hw.ρ_pos
  set γ := walk ch ℓ p₀ with hγ
  have hγc : Continuous γ := hw.continuous_walk
  set A : Set ℝ := {s | 0 ≤ s ∧ ∃ t, s < t ∧ t ≤ t₀ ∧ γ s = γ t} with hA
  have hs₀A : s₀ ∈ A := ⟨hs₀, t₀, hst, le_rfl, heq⟩
  have hbdd : BddBelow A := ⟨0, fun s hs => hs.1⟩
  set s₁ := sInf A with hs₁
  have hs₁0 : 0 ≤ s₁ := le_csInf ⟨s₀, hs₀A⟩ fun s hs => hs.1
  obtain ⟨u, -, hu, huA⟩ := exists_seq_tendsto_sInf ⟨s₀, hs₀A⟩ hbdd
  choose t ht using fun n => (huA n).2
  have htI : ∀ n, t n ∈ Icc 0 t₀ := fun n => ⟨by linarith [(huA n).1, (ht n).1], (ht n).2.1⟩
  obtain ⟨t₁, ht₁I, φ, hφ, htφ⟩ := isCompact_Icc.tendsto_subseq htI
  have huφ : Tendsto (u ∘ φ) atTop (𝓝 s₁) := hu.comp hφ.tendsto_atTop
  have hγeq : γ s₁ = γ t₁ := by
    have h1 := (hγc.tendsto s₁).comp huφ
    have h2 := (hγc.tendsto t₁).comp htφ
    have : (γ ∘ (u ∘ φ)) = (γ ∘ (t ∘ φ)) := funext fun n => (ht (φ n)).2.2
    rw [this] at h1
    exact tendsto_nhds_unique h1 h2
  have hle : s₁ ≤ t₁ := le_of_tendsto_of_tendsto' huφ htφ fun n => (ht (φ n)).1.le
  have hlt : s₁ < t₁ := by
    refine lt_of_le_of_ne hle fun hEq => ?_
    obtain ⟨ε, hε, hinj⟩ := hw.locally_injective hs₁0
    have hI : Icc (s₁ - ε) (s₁ + ε) ∈ 𝓝 s₁ := Icc_mem_nhds (by linarith) (by linarith)
    rw [← hEq] at htφ
    have e1 : ∀ᶠ n in atTop, (u ∘ φ) n ∈ Icc (s₁ - ε) (s₁ + ε) := huφ hI
    have e2 : ∀ᶠ n in atTop, (t ∘ φ) n ∈ Icc (s₁ - ε) (s₁ + ε) := htφ hI
    obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
    have := hinj hn1 hn2 (ht (φ n)).2.2
    exact absurd this (ht (φ n)).1.ne
  rcases lt_or_eq_of_le hs₁0 with hs₁pos | hs₁0'
  swap
  · exact ⟨t₁, by linarith, ht₁I.2, by rw [← hγeq, ← hs₁0']⟩
  exfalso
  -- backward step at the pair `(s₁, t₁)`
  set P := γ s₁ with hP
  have hPf : P ∈ frontier Ω := hw.walk_mem_frontier (by linarith)
  have hch := hw.chart P hPf
  set c := (ch P).1
  have hboxs : γ s₁ ∈ chartBox P c ρ H := hch.center_mem_box
  have hboxt : γ t₁ ∈ chartBox P c ρ H := by rw [← hγeq]; exact hboxs
  obtain ⟨ε₁, hε₁, hm₁⟩ := hw.walk_local_strictMono hs₁0 hch hboxs
  obtain ⟨ε₂, hε₂, hm₂⟩ := hw.walk_local_strictMono (by linarith) hch hboxt
  obtain ⟨ε₃, hε₃, hb₃⟩ := hw.eventually_box hboxs
  obtain ⟨ε₄, hε₄, hb₄⟩ := hw.eventually_box hboxt
  set ε := min (min ε₁ ε₂) (min (min ε₃ ε₄) (min (s₁ / 2) ((t₁ - s₁) / 2))) with hε
  have hεpos : 0 < ε := lt_min (lt_min hε₁ hε₂)
    (lt_min (lt_min hε₃ hε₄) (lt_min (by linarith) (by linarith)))
  have hε1 : ε ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε2 : ε ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε3 : ε ≤ ε₃ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε4 : ε ≤ ε₄ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε5 : ε ≤ s₁ / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε6 : ε ≤ (t₁ - s₁) / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set g := walkX ch ℓ p₀ P c with hg
  have hgc : Continuous g := hw.continuous_walkX P c
  have hgst : g s₁ = g t₁ := by
    change (c * (γ s₁ - P)).re = (c * (γ t₁ - P)).re; rw [← hγeq, ← hP]
  set L := g (t₁ - ε)
  have hLt : L < g t₁ := hm₂ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    (by linarith)
  have hev1 : ∀ᶠ s in 𝓝 s₁, L < g s :=
    (hgc.tendsto s₁).eventually (lt_mem_nhds (by rw [hgst]; exact hLt))
  have hev2 : ∀ᶠ s in 𝓝[<] s₁, s ∈ Ioo (s₁ - ε) s₁ := Ioo_mem_nhdsLT (by linarith)
  have hev : ∀ᶠ s in 𝓝[<] s₁, L < g s ∧ s ∈ Ioo (s₁ - ε) s₁ :=
    (eventually_nhdsWithin_of_eventually_nhds hev1).and hev2
  obtain ⟨s', hs'L, hs'I⟩ := hev.exists
  have hgs' : g s' < g s₁ := hm₁ ⟨by linarith [hs'I.1], by linarith [hs'I.2]⟩
    ⟨by linarith, by linarith⟩ hs'I.2
  have hs'f : γ s' ∈ frontier Ω := hw.walk_mem_frontier (by linarith [hs'I.1])
  have hs'b : γ s' ∈ chartBox P c ρ H := hb₃ s' ⟨by linarith [hs'I.1], by linarith [hs'I.2]⟩
  obtain ⟨t', ht'I, ht'eq⟩ := hw.capture (α := t₁ - ε) (β := t₁) (by linarith) (by linarith)
    hch (fun s hs => hb₄ s ⟨by linarith [hs.1], by linarith [hs.2]⟩) hs'f hs'b hs'L.le
    (by change g s' ≤ g t₁; rw [← hgst]; exact hgs'.le)
  have hs'A : s' ∈ A := ⟨by linarith [hs'I.1], t', by linarith [ht'I.1, hs'I.2], by
    linarith [ht'I.2, ht₁I.2], ht'eq.symm⟩
  have := csInf_le hbdd hs'A
  linarith [hs'I.2]

/-- **The first return.** If the walk revisits a point, there is a first return time `T > 0` to
the starting point, and the walk is injective on `[0, T)`. -/
theorem WalkData.exists_loop (hw : WalkData Ω ρ H K ch ℓ p₀) {s₀ t₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hst : s₀ < t₀) (heq : walk ch ℓ p₀ s₀ = walk ch ℓ p₀ t₀) :
    ∃ T, 0 < T ∧ walk ch ℓ p₀ T = walk ch ℓ p₀ 0 ∧ InjOn (walk ch ℓ p₀) (Ico 0 T) := by
  obtain ⟨ε₀, hε₀, hinj₀⟩ := hw.locally_injective (s := 0) le_rfl
  set S : Set ℝ := {t | ε₀ ≤ t ∧ walk ch ℓ p₀ t = walk ch ℓ p₀ 0} with hS
  have hmemS : ∀ T, 0 < T → walk ch ℓ p₀ T = walk ch ℓ p₀ 0 → T ∈ S := fun T hT hTeq => by
    refine ⟨not_lt.mp fun hlt => ?_, hTeq⟩
    have := hinj₀ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hTeq
    linarith
  obtain ⟨T₁, hT₁, -, hT₁eq⟩ := hw.exists_return hs₀ hst heq
  have hSne : S.Nonempty := ⟨T₁, hmemS T₁ hT₁ hT₁eq⟩
  have hSbdd : BddBelow S := ⟨ε₀, fun t ht => ht.1⟩
  have hScl : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_eq hw.continuous_walk continuous_const)
  set T := sInf S
  have hTS : T ∈ S := hScl.csInf_mem hSne hSbdd
  refine ⟨T, by linarith [hTS.1], hTS.2, fun a ha b hb hab => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨T', hT', hT'b, hT'eq⟩ := hw.exists_return ha.1 hlt hab
    have := csInf_le hSbdd (hmemS T' hT' hT'eq)
    linarith [hb.2]
  · obtain ⟨T', hT', hT'a, hT'eq⟩ := hw.exists_return hb.1 hlt hab.symm
    have := csInf_le hSbdd (hmemS T' hT' hT'eq)
    linarith [ha.2]

/-- **The walk revisits a point**, by compactness of the boundary. Here the step `ℓ` is small
compared with the uniform chart size. -/
theorem WalkData.exists_pair (hw : WalkData Ω ρ H K ch ℓ p₀) (hcpt : IsCompact (frontier Ω))
    (hℓsmall : (1 + K) * ℓ ≤ min ρ H / 2) :
    ∃ s₀ t₀, 0 ≤ s₀ ∧ s₀ < t₀ ∧ walk ch ℓ p₀ s₀ = walk ch ℓ p₀ t₀ := by
  have hℓ := hw.ℓ_pos
  have hK1 : (0 : ℝ) < 1 + K := by positivity
  set q : ℕ → ℂ := walkPt ch ℓ p₀ with hq
  obtain ⟨P, hPf, φ, hφ, hqφ⟩ := hcpt.tendsto_subseq (x := q) hw.walkPt_mem
  have hch := hw.chart P hPf
  set c := (ch P).1
  set m₀ := min ρ H with hm₀
  have hm₀pos : 0 < m₀ := lt_min hw.ρ_pos (by linarith [hch.2.2.1])
  have hball : ball P m₀ ⊆ chartBox P c ρ H := ball_subset_chartBox hch.1
  set δ := min (m₀ / 4) (ℓ / (2 * (1 + K))) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hqφ δ hδpos
  set n := φ (N + 1) with hn
  set m := φ (N + 3) with hm
  have hn1 : 1 ≤ n := by
    show 1 ≤ φ (N + 1)
    have := hφ (show N < N + 1 by omega); omega
  have hmn : n + 2 ≤ m := by
    have h1 := hφ (show N + 1 < N + 2 by omega)
    have h2 := hφ (show N + 2 < N + 3 by omega)
    omega
  have hqn : dist (q n) P < δ := hN (N + 1) (by omega)
  have hqm : dist (q m) P < δ := hN (N + 3) (by omega)
  have hwn : walk ch ℓ p₀ (n * ℓ) = q n := by
    have := hw.walk_eq n (u := 0) ⟨le_rfl, hℓ.le⟩
    rw [add_zero] at this
    rw [this, hw.stepCurve_zero (hw.walkPt_mem n)]
  have hwm : walk ch ℓ p₀ (m * ℓ) = q m := by
    have := hw.walk_eq m (u := 0) ⟨le_rfl, hℓ.le⟩
    rw [add_zero] at this
    rw [this, hw.stepCurve_zero (hw.walkPt_mem m)]
  have hL := hw.lipschitzWith_walk
  -- the walk around time `n ℓ` stays in the chart box at `P`
  have hbox : ∀ s ∈ Icc ((n : ℝ) * ℓ - ℓ) (n * ℓ + ℓ), walk ch ℓ p₀ s ∈ chartBox P c ρ H := by
    intro s hs
    refine hball ?_
    rw [mem_ball]
    have h1 : dist (walk ch ℓ p₀ s) (walk ch ℓ p₀ (n * ℓ)) ≤ (1 + K) * dist s (n * ℓ) := by
      have := hL.dist_le_mul s (n * ℓ); push_cast at this; exact this
    have h2 : dist s (n * ℓ) ≤ ℓ := by
      rw [Real.dist_eq, abs_le]; constructor <;> linarith [hs.1, hs.2]
    calc dist (walk ch ℓ p₀ s) P ≤ dist (walk ch ℓ p₀ s) (walk ch ℓ p₀ (n * ℓ)) +
          dist (walk ch ℓ p₀ (n * ℓ)) P := dist_triangle _ _ _
      _ < (1 + K) * ℓ + m₀ / 4 := by
          rw [hwn] at h1 ⊢
          have := mul_le_mul_of_nonneg_left h2 hK1.le
          have := min_le_left (m₀ / 4) (ℓ / (2 * (1 + K)))
          linarith
      _ < m₀ := by linarith
  have hα : (0 : ℝ) ≤ n * ℓ - ℓ := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  have hmono := hw.strictMonoOn_walkX hα hch hbox
  set g := walkX ch ℓ p₀ P c with hg
  have hfr : ∀ s, 0 ≤ s → walk ch ℓ p₀ s ∈ frontier Ω := fun s hs =>
    hw.walk_mem_frontier (by linarith [hw.ρ_pos])
  -- abscissa increments over one step on each side
  have hdist : ∀ s₁ s₂, s₁ ∈ Icc ((n : ℝ) * ℓ - ℓ) (n * ℓ + ℓ) →
      s₂ ∈ Icc ((n : ℝ) * ℓ - ℓ) (n * ℓ + ℓ) → s₁ < s₂ →
      ‖walk ch ℓ p₀ s₂ - walk ch ℓ p₀ s₁‖ ≤ (1 + K) * (g s₂ - g s₁) := by
    intro s₁ s₂ hs₁ hs₂ h12
    have := norm_sub_le_of_frontier hw.isOpen hch (hfr s₂ (by linarith [hs₂.1]))
      (hfr s₁ (by linarith [hs₁.1])) (hbox s₂ hs₂) (hbox s₁ hs₁)
    have hlt : g s₁ < g s₂ := hmono hs₁ hs₂ h12
    rwa [abs_of_pos (by simp only [hg, walkX] at hlt ⊢; linarith)] at this
  have hright : ℓ / (1 + K) ≤ g (n * ℓ + ℓ) - g (n * ℓ) := by
    have h1 := hw.le_norm_walk_sub n (u := 0) (u' := ℓ) ⟨le_rfl, hℓ.le⟩ ⟨hℓ.le, le_rfl⟩
    rw [add_zero, sub_zero, abs_of_pos hℓ] at h1
    have h2 := hdist (n * ℓ) (n * ℓ + ℓ) ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩
      (by linarith)
    rw [div_le_iff₀ hK1]; nlinarith
  have hleft : ℓ / (1 + K) ≤ g (n * ℓ) - g (n * ℓ - ℓ) := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 := hw.le_norm_walk_sub k (u := 0) (u' := ℓ) ⟨le_rfl, hℓ.le⟩ ⟨hℓ.le, le_rfl⟩
    rw [add_zero, abs_of_pos (by linarith)] at h1
    have e1 : (k : ℝ) * ℓ + ℓ = n * ℓ := by rw [hk]; push_cast; ring
    have e2 : (k : ℝ) * ℓ = n * ℓ - ℓ := by rw [hk]; push_cast; ring
    rw [e1, e2, sub_zero] at h1
    have h2 := hdist (n * ℓ - ℓ) (n * ℓ) ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩
      (by linarith)
    rw [div_le_iff₀ hK1]; nlinarith
  -- the abscissa of `q m` is close to that of `q n`
  have hqmf : q m ∈ frontier Ω := hw.walkPt_mem m
  have hqmb : q m ∈ chartBox P c ρ H := hball (lt_of_lt_of_le hqm (by
    have := min_le_left (m₀ / 4) (ℓ / (2 * (1 + K))); linarith))
  have hXclose : |(c * (q m - P)).re - g (n * ℓ)| ≤ 2 * δ := by
    have hgn : g (n * ℓ) = (c * (q n - P)).re := by simp only [hg, walkX, hwn]
    rw [hgn, ← Complex.sub_re, ← mul_sub, sub_sub_sub_cancel_right]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul, hch.1, one_mul]
    have := dist_triangle (q m) P (q n)
    rw [dist_comm P, dist_eq_norm] at this
    linarith
  have h2δ : 2 * δ ≤ ℓ / (1 + K) := by
    have := min_le_right (m₀ / 4) (ℓ / (2 * (1 + K)))
    have e : ℓ / (2 * (1 + K)) = ℓ / (1 + K) / 2 := by field_simp
    linarith
  rw [abs_le] at hXclose
  obtain ⟨s, hs, hseq⟩ := hw.capture (α := n * ℓ - ℓ) (β := n * ℓ + ℓ)
    (by linarith [hw.ρ_pos]) (by linarith) hch hbox hqmf hqmb
    (by linarith) (by linarith)
  refine ⟨s, m * ℓ, by linarith [hs.1], ?_, by rw [hseq, hwm]⟩
  have : ((n : ℝ) + 2) ≤ m := by exact_mod_cast hmn
  nlinarith [hs.2]

/-- Near a point of the walk where the abscissa is strictly increasing and the walk is in the
box, boundary points with abscissa in the corresponding range are on the walk. -/
lemma WalkData.exists_nhd_subset (hw : WalkData Ω ρ H K ch ℓ p₀) {α β : ℝ} (hα : 0 ≤ α)
    (hαβ : α ≤ β) {p c : ℂ} {r h : ℝ} {K' : NNReal} {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K' f)
    (hbox : ∀ s ∈ Icc α β, walk ch ℓ p₀ s ∈ chartBox p c r h) :
    ∀ w ∈ frontier Ω ∩ (chartBox p c r h ∩ {w | walkX ch ℓ p₀ p c α < (c * (w - p)).re ∧
      (c * (w - p)).re < walkX ch ℓ p₀ p c β}), ∃ s ∈ Icc α β, walk ch ℓ p₀ s = w :=
  fun w ⟨hwf, hwb, h1, h2⟩ =>
    hw.capture (by linarith [hw.ρ_pos]) hαβ hch hbox hwf hwb h1.le h2.le

lemma isOpen_abscissa_band (p c : ℂ) (a b : ℝ) :
    IsOpen {w : ℂ | a < (c * (w - p)).re ∧ (c * (w - p)).re < b} := by
  have hg : Continuous fun w : ℂ => (c * (w - p)).re := by fun_prop
  exact (isOpen_lt continuous_const hg).inter (isOpen_lt hg continuous_const)

/-- **The loop fills the boundary.** If `∂Ω` is preconnected and the walk returns to its start at
time `T > 0`, then the walk on `[0, T]` covers `∂Ω`. -/
theorem WalkData.image_eq (hw : WalkData Ω ρ H K ch ℓ p₀) {T : ℝ} (hT : 0 < T)
    (hTeq : walk ch ℓ p₀ T = walk ch ℓ p₀ 0) (hconn : IsPreconnected (frontier Ω)) :
    walk ch ℓ p₀ '' Icc 0 T = frontier Ω := by
  have hρ := hw.ρ_pos
  set γ := walk ch ℓ p₀ with hγ
  set Im := γ '' Icc 0 T with hIm
  have hsub : Im ⊆ frontier Ω := by
    rintro _ ⟨t, ht, rfl⟩; exact hw.walk_mem_frontier (by linarith [ht.1])
  refine subset_antisymm hsub ?_
  have hImc : IsClosed Im := (isCompact_Icc.image hw.continuous_walk).isClosed
  -- every point of the loop has a neighbourhood whose boundary points are on the loop
  have hloc : ∀ t ∈ Icc 0 T, ∃ V : Set ℂ, IsOpen V ∧ γ t ∈ V ∧ frontier Ω ∩ V ⊆ Im := by
    intro t ht
    have hPf : γ t ∈ frontier Ω := hsub ⟨t, ht, rfl⟩
    set P := γ t
    have hch := hw.chart P hPf
    set c := (ch P).1
    set g := walkX ch ℓ p₀ P c with hg
    have hPb : P ∈ chartBox P c ρ H := hch.center_mem_box
    by_cases hend : t = 0 ∨ t = T
    · -- the starting point: forward from `0` and backward from `T`
      have hP0 : γ 0 = P := by rcases hend with h | h <;> simp only [P, h, hTeq]
      have hb0 : γ 0 ∈ chartBox P c ρ H := by rw [hP0]; exact hPb
      have hbT : γ T ∈ chartBox P c ρ H := by rw [hTeq, hP0]; exact hPb
      obtain ⟨ε₁, hε₁, hm₁⟩ := hw.walk_local_strictMono le_rfl hch hb0
      obtain ⟨ε₂, hε₂, hb₂⟩ := hw.eventually_box hb0
      obtain ⟨ε₃, hε₃, hm₃⟩ := hw.walk_local_strictMono hT.le hch hbT
      obtain ⟨ε₄, hε₄, hb₄⟩ := hw.eventually_box hbT
      set ε := min (min ε₁ ε₂) (min (min ε₃ ε₄) T) with hε
      have hεpos : 0 < ε := lt_min (lt_min hε₁ hε₂) (lt_min (lt_min hε₃ hε₄) hT)
      have hε1 : ε ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
      have hε2 : ε ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
      have hε3 : ε ≤ ε₃ :=
        le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
      have hε4 : ε ≤ ε₄ :=
        le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
      have hεT : ε ≤ T := le_trans (min_le_right _ _) (min_le_right _ _)
      have hg0 : g 0 = g T := by simp only [hg, walkX, ← hγ, hTeq]
      have hgε : g 0 < g ε := hm₁ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hεpos
      have hgT : g (T - ε) < g T := hm₃ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        (by linarith)
      have hgP : g 0 = (c * (P - P)).re := by simp only [hg, walkX, ← hγ, hP0]
      refine ⟨chartBox P c ρ H ∩ {w | g (T - ε) < (c * (w - P)).re ∧ (c * (w - P)).re < g ε},
        (isOpen_chartBox _ _ _ _).inter (isOpen_abscissa_band _ _ _ _), ⟨hPb, ?_, ?_⟩, ?_⟩
      · rw [← hgP, hg0]; exact hgT
      · rw [← hgP]; exact hgε
      · rintro w ⟨hwf, hwb, h1, h2⟩
        rcases le_or_gt (g 0) (c * (w - P)).re with hle | hlt
        · obtain ⟨s, hs, hseq⟩ := hw.capture (α := 0) (β := ε) (by linarith) hεpos.le hch
            (fun s hs => hb₂ s ⟨by linarith [hs.1], by linarith [hs.2]⟩) hwf hwb hle h2.le
          exact ⟨s, ⟨hs.1, by linarith [hs.2]⟩, hseq⟩
        · obtain ⟨s, hs, hseq⟩ := hw.capture (α := T - ε) (β := T) (by linarith) (by linarith)
            hch (fun s hs => hb₄ s ⟨by linarith [hs.1], by linarith [hs.2]⟩) hwf hwb h1.le
            (by change _ ≤ g T; rw [← hg0]; exact hlt.le)
          exact ⟨s, ⟨by linarith [hs.1], hs.2⟩, hseq⟩
    · push_neg at hend
      have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hend.1)
      have htT : t < T := lt_of_le_of_ne ht.2 hend.2
      obtain ⟨ε₁, hε₁, hm₁⟩ := hw.walk_local_strictMono ht.1 hch hPb
      obtain ⟨ε₂, hε₂, hb₂⟩ := hw.eventually_box (s := t) hPb
      set ε := min (min ε₁ ε₂) (min t (T - t)) with hε
      have hεpos : 0 < ε := lt_min (lt_min hε₁ hε₂) (lt_min ht0 (by linarith))
      have hε1 : ε ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
      have hε2 : ε ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
      have hε3 : ε ≤ t := le_trans (min_le_right _ _) (min_le_left _ _)
      have hε4 : ε ≤ T - t := le_trans (min_le_right _ _) (min_le_right _ _)
      have hgP : g t = (c * (P - P)).re := rfl
      refine ⟨chartBox P c ρ H ∩ {w | g (t - ε) < (c * (w - P)).re ∧
        (c * (w - P)).re < g (t + ε)},
        (isOpen_chartBox _ _ _ _).inter (isOpen_abscissa_band _ _ _ _), ⟨hPb, ?_, ?_⟩, ?_⟩
      · rw [← hgP]
        exact hm₁ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
      · rw [← hgP]
        exact hm₁ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
      · intro w hw'
        obtain ⟨s, hs, hseq⟩ := hw.exists_nhd_subset (α := t - ε) (β := t + ε) (by linarith)
          (by linarith) hch (fun s hs => hb₂ s ⟨by linarith [hs.1], by linarith [hs.2]⟩) w hw'
        exact ⟨s, ⟨by linarith [hs.1], by linarith [hs.2]⟩, hseq⟩
  choose! V hVo hVmem hVsub using hloc
  set U := ⋃ t ∈ Icc 0 T, V t with hU
  have hUo : IsOpen U := isOpen_biUnion fun t ht => hVo t ht
  have hcover : frontier Ω ⊆ U ∪ Imᶜ := fun x hx => by
    by_cases hxI : x ∈ Im
    · obtain ⟨t, ht, rfl⟩ := hxI
      exact Or.inl (mem_biUnion ht (hVmem t ht))
    · exact Or.inr hxI
  have hdisj : frontier Ω ∩ (U ∩ Imᶜ) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hx hxU hxI
    obtain ⟨t, ht, hxV⟩ := mem_iUnion₂.mp hxU
    exact hxI (hVsub t ht ⟨hx, hxV⟩)
  rcases (isPreconnected_iff_subset_of_disjoint.mp hconn) U Imᶜ hUo hImc.isOpen_compl hcover
    hdisj with h | h
  · intro x hx
    obtain ⟨t, ht, hxV⟩ := mem_iUnion₂.mp (h hx)
    exact hVsub t ht ⟨hx, hxV⟩
  · exfalso
    have h0 : γ 0 ∈ Im := ⟨0, ⟨le_rfl, hT.le⟩, rfl⟩
    exact h (hsub h0) h0

end Loop

/-- A Lipschitz closed curve on `[0, T]`, injective on `[0, T)`, reparametrized linearly to
`[0, 2π]` and extended periodically, gives a Lipschitz `2π`-periodic curve injective on
`[0, 2π)` with the same image. -/
theorem exists_periodic_of_loop {Γ : ℝ → ℂ} {K : NNReal} (hΓ : LipschitzWith K Γ) {T : ℝ}
    (hT : 0 < T) (hcl : Γ T = Γ 0) (hinj : InjOn Γ (Ico 0 T)) :
    ∃ γ : ℝ → ℂ, (∃ K', LipschitzWith K' γ) ∧ Function.Periodic γ (2 * π) ∧
      InjOn γ (Ico 0 (2 * π)) ∧ γ '' Icc 0 (2 * π) = Γ '' Icc 0 T := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set a : ℝ := T / (2 * π) with ha
  have ha0 : 0 < a := by positivity
  set G : ℝ → ℂ := fun θ => Γ (a * θ) with hG
  have hGL : LipschitzWith (K * ⟨a, ha0.le⟩) G := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := hΓ.dist_le_mul (a * x) (a * y)
    simp only [hG, Real.dist_eq] at this ⊢
    rw [← mul_sub, abs_mul, abs_of_pos ha0] at this
    -- Local port: expose the nonnegative-real coercion before reassociation.
    change dist (Γ (a * x)) (Γ (a * y)) ≤ ((K : ℝ) * a) * |x - y|
    simpa only [mul_assoc] using this
  have hG2π : G (2 * π) = G 0 := by
    simp only [hG, mul_zero, ha]; rw [div_mul_cancel₀ _ h2π.ne', hcl]
  set γ : ℝ → ℂ := fun θ => G (toIcoMod h2π 0 θ) with hγ
  have hγ_Ico : ∀ θ ∈ Ico 0 (2 * π), γ θ = G θ := fun θ hθ => by
    simp only [hγ]; rw [(toIcoMod_eq_self h2π).mpr (by simpa using hθ)]
  have hγ_piece : ∀ n : ℤ, ∀ θ ∈ Icc (n * (2 * π)) ((n + 1) * (2 * π)),
      γ θ = G (θ - n * (2 * π)) := by
    intro n θ hθ
    rcases lt_or_eq_of_le hθ.2 with hlt | heq
    · simp only [hγ]
      rw [← toIcoMod_sub_zsmul h2π 0 θ n, zsmul_eq_mul,
        (toIcoMod_eq_self h2π).mpr ⟨by linarith [hθ.1], by linarith⟩]
    · have h1 : γ θ = G 0 := by
        simp only [hγ]
        rw [← toIcoMod_sub_zsmul h2π 0 θ (n + 1), zsmul_eq_mul, heq]
        push_cast
        rw [sub_self, (toIcoMod_eq_self h2π).mpr ⟨le_rfl, by linarith⟩]
      rw [h1, heq, show ((n : ℝ) + 1) * (2 * π) - n * (2 * π) = 2 * π by ring, hG2π]
  refine ⟨γ, ⟨K * ⟨a, ha0.le⟩, ?_⟩, ?_, ?_, ?_⟩
  · refine lipschitzWith_of_pieces h2π fun n => LipschitzOnWith.of_dist_le_mul
      fun x hx y hy => ?_
    rw [hγ_piece n x hx, hγ_piece n y hy]
    have := hGL.dist_le_mul (x - n * (2 * π)) (y - n * (2 * π))
    rwa [Real.dist_eq, sub_sub_sub_cancel_right, ← Real.dist_eq] at this
  · intro θ
    simp only [hγ, toIcoMod_add_right]
  · intro x hx y hy hxy
    rw [hγ_Ico x hx, hγ_Ico y hy] at hxy
    have := hinj ⟨by have := hx.1; positivity, by
        have := hx.2; rw [ha]; rw [div_mul_eq_mul_div, div_lt_iff₀ h2π]; nlinarith⟩
      ⟨by have := hy.1; positivity, by
        have := hy.2; rw [ha]; rw [div_mul_eq_mul_div, div_lt_iff₀ h2π]; nlinarith⟩ hxy
    exact mul_left_cancel₀ ha0.ne' this
  · have hγ_Icc : ∀ θ ∈ Icc 0 (2 * π), γ θ = Γ (a * θ) := fun θ hθ => by
      have := hγ_piece 0 θ ⟨by simpa using hθ.1, by simpa using hθ.2⟩
      simpa using this
    ext w
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      refine ⟨a * θ, ⟨by have := hθ.1; positivity, ?_⟩, (hγ_Icc θ hθ).symm⟩
      have := hθ.2; rw [ha, div_mul_eq_mul_div, div_le_iff₀ h2π]; nlinarith
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t / a, ⟨div_nonneg ht.1 ha0.le, ?_⟩, ?_⟩
      · rw [div_le_iff₀ ha0, ha, mul_div_cancel₀ _ h2π.ne']; exact ht.2
      · rw [hγ_Icc _ ⟨div_nonneg ht.1 ha0.le, by
          rw [div_le_iff₀ ha0, ha, mul_div_cancel₀ _ h2π.ne']; exact ht.2⟩,
          mul_div_cancel₀ _ ha0.ne']

/-- **A Lipschitz Jordan loop in the boundary.** A bounded Lipschitz domain has a Lipschitz
`2π`-periodic curve `γ`, injective on `[0, 2π)`, with image in `∂Ω`; if `∂Ω` is connected, the
image is all of `∂Ω`. -/
theorem exists_jordanLoop_frontier {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) :
    ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * π) ∧
      InjOn γ (Ico 0 (2 * π)) ∧ γ '' Icc 0 (2 * π) ⊆ frontier Ω ∧
      (IsPreconnected (frontier Ω) → γ '' Icc 0 (2 * π) = frontier Ω) := by
  obtain ⟨ρ, H, K, hρ, hH, hKρ, hcharts⟩ := exists_uniform_charts hb hL
  choose! c f hcf using hcharts
  set ch : ℂ → ℂ × (ℝ → ℝ) := fun p => (c p, f p) with hch
  obtain ⟨p₀, hp₀⟩ : (frontier Ω).Nonempty := by
    refine nonempty_frontier_iff.mpr ⟨hL.1.2.nonempty, fun huniv => ?_⟩
    have := hb
    rw [huniv] at this
    exact NormedSpace.unbounded_univ ℝ ℂ this
  have hK1 : (0 : ℝ) < 1 + K := by positivity
  set ℓ : ℝ := min ρ H / (2 * (1 + K)) with hℓ
  have hm : 0 < min ρ H := lt_min hρ hH
  have hℓpos : 0 < ℓ := by positivity
  have hℓρ : ℓ < ρ := by
    have : ℓ ≤ min ρ H / 2 := by
      rw [hℓ]; apply div_le_div_of_nonneg_left hm.le (by norm_num); linarith [NNReal.coe_nonneg K]
    have := min_le_left ρ H
    linarith
  have hw : WalkData Ω ρ H K ch ℓ p₀ :=
    ⟨hL.1.1, fun p hp => hcf p hp, hℓpos, hℓρ, hp₀⟩
  have hsmall : (1 + K) * ℓ ≤ min ρ H / 2 := by
    rw [hℓ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨s₀, t₀, hs₀, hst, heq⟩ := hw.exists_pair (frontier_isCompact hb) hsmall
  obtain ⟨T, hT, hTeq, hinj⟩ := hw.exists_loop hs₀ hst heq
  obtain ⟨γ, hγL, hγp, hγi, hγim⟩ := exists_periodic_of_loop hw.lipschitzWith_walk hT hTeq hinj
  refine ⟨γ, hγL, hγp, hγi, ?_, fun hconn => by rw [hγim, hw.image_eq hT hTeq hconn]⟩
  rw [hγim]
  rintro _ ⟨t, ht, rfl⟩
  exact hw.walk_mem_frontier (by linarith [ht.1])

/-- **External theorem E3, boundary description, for connected boundaries.** If `Ω` is a bounded
Lipschitz domain whose boundary is connected, then `∂Ω` is a single Lipschitz Jordan curve: it
has a Lipschitz `2π`-periodic parametrization, injective on `[0, 2π)`, with image `∂Ω`. -/
theorem exists_jordanParam_of_isPreconnected_frontier {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hconn : IsPreconnected (frontier Ω)) :
    ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * π) ∧
      InjOn γ (Ico 0 (2 * π)) ∧ γ '' Icc 0 (2 * π) = frontier Ω := by
  obtain ⟨γ, hγL, hγp, hγi, -, hγim⟩ := exists_jordanLoop_frontier hb hL
  exact ⟨γ, hγL, hγp, hγi, hγim hconn⟩

end PolyaNeumann
