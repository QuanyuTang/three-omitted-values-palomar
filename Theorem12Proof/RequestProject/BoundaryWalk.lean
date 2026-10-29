module

public import Theorem12Proof.RequestProject.BoundaryChart

/-!
# Walking along a Lipschitz boundary

Given uniform charts `ch p` at the boundary points `p` of a Lipschitz domain, the *boundary
walk* starting at `p₀` with step `ℓ` follows the graph of the chart at the current point for
abscissae `0 ≤ x ≤ ℓ`, then moves to the chart at the point reached, and so on. The walk is a
Lipschitz curve along `∂Ω` (`lipschitzWith_walk`, `walk_mem_frontier`), and in every chart its
abscissa is locally strictly increasing (`walk_local_strictMono`), by consistency of
orientation (`chart_orient`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-! ### Gluing Lipschitz pieces -/

/-- A function which is `K`-Lipschitz on every interval `[n p, (n + 1) p]` (`n ∈ ℤ`) is
`K`-Lipschitz. -/
lemma lipschitzWith_of_pieces {f : ℝ → ℂ} {K : NNReal} {p : ℝ} (hp : 0 < p)
    (h : ∀ n : ℤ, LipschitzOnWith K f (Icc (n * p) ((n + 1) * p))) : LipschitzWith K f := by
  have key : ∀ k : ℕ, ∀ x y : ℝ, x ≤ y → ⌊y / p⌋ = ⌊x / p⌋ + k →
      dist (f x) (f y) ≤ K * dist x y := by
    intro k
    induction k with
    | zero =>
      intro x y hxy hfl
      have hx := Int.floor_le (x / p)
      have hx' := Int.lt_floor_add_one (x / p)
      have hy := Int.floor_le (y / p)
      have hy' := Int.lt_floor_add_one (y / p)
      simp only [Nat.cast_zero, add_zero] at hfl
      rw [hfl] at hy hy'
      set n := ⌊x / p⌋
      have hmem : ∀ z, (n : ℝ) ≤ z / p → z / p < n + 1 → z ∈ Icc (n * p) ((n + 1) * p) :=
        fun z h1 h2 => ⟨by rwa [le_div_iff₀ hp] at h1, by rw [div_lt_iff₀ hp] at h2; linarith⟩
      exact (h n).dist_le_mul x (hmem x hx hx') y (hmem y hy hy')
    | succ k ih =>
      intro x y hxy hfl
      set n := ⌊x / p⌋
      set b : ℝ := (n + 1) * p
      have hx := Int.floor_le (x / p)
      have hx' := Int.lt_floor_add_one (x / p)
      have hxb : x ≤ b := by
        have : x / p < n + 1 := hx'
        rw [div_lt_iff₀ hp] at this; exact this.le
      have hbfl : ⌊b / p⌋ = n + 1 := by
        simp only [b]; rw [mul_div_cancel_right₀ _ hp.ne']; exact_mod_cast Int.floor_intCast (n + 1)
      have hby : b ≤ y := by
        have h1 : ((n + 1 : ℤ) : ℝ) ≤ ⌊y / p⌋ := by
          rw [hfl]; push_cast; linarith
        have h2 := Int.floor_le (y / p)
        have : (n + 1 : ℝ) ≤ y / p := by push_cast at h1; linarith
        rw [le_div_iff₀ hp] at this; exact this
      have h1 : dist (f x) (f b) ≤ K * dist x b := by
        refine (h n).dist_le_mul x ⟨?_, hxb⟩ b ⟨?_, le_rfl⟩
        · have : (n : ℝ) ≤ x / p := hx
          rwa [le_div_iff₀ hp] at this
        · simp only [b]; nlinarith
      have h2 : dist (f b) (f y) ≤ K * dist b y :=
        ih b y hby (by rw [hfl, hbfl]; push_cast; ring)
      calc dist (f x) (f y) ≤ dist (f x) (f b) + dist (f b) (f y) := dist_triangle _ _ _
        _ ≤ K * dist x b + K * dist b y := add_le_add h1 h2
        _ = K * dist x y := by
          rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith),
            abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rcases le_total x y with hxy | hxy
  · have hfl : ⌊x / p⌋ ≤ ⌊y / p⌋ := Int.floor_mono (div_le_div_of_nonneg_right hxy hp.le)
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hfl)
    exact key k x y hxy (by omega)
  · have hfl : ⌊y / p⌋ ≤ ⌊x / p⌋ := Int.floor_mono (div_le_div_of_nonneg_right hxy hp.le)
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hfl)
    rw [dist_comm, dist_comm x]
    exact key k y x hxy (by omega)

/-- Gluing strict monotonicity on two adjacent closed intervals. -/
lemma strictMonoOn_Icc_union {g : ℝ → ℝ} {a t b : ℝ} (h1 : StrictMonoOn g (Icc a t))
    (h2 : StrictMonoOn g (Icc t b)) : StrictMonoOn g (Icc a b) := by
  intro x hx y hy hxy
  rcases le_total y t with hyt | hyt
  · exact h1 ⟨hx.1, by linarith⟩ ⟨hy.1, hyt⟩ hxy
  rcases le_total t x with htx | htx
  · exact h2 ⟨htx, hx.2⟩ ⟨hyt, hy.2⟩ hxy
  rcases lt_or_eq_of_le htx with htx' | htx'
  · calc g x < g t := h1 ⟨hx.1, htx⟩ ⟨by linarith [hx.1], le_rfl⟩ htx'
      _ ≤ g y := (h2.monotoneOn) ⟨le_rfl, by linarith [hy.2]⟩ ⟨hyt, hy.2⟩ hyt
  · rw [htx']; exact h2 ⟨le_rfl, by linarith [hy.2]⟩ ⟨hyt, hy.2⟩ (by rw [← htx']; exact hxy)

/-! ### The walk -/

/-- The graph curve of the chart chosen at `q`. -/
def stepCurve (ch : ℂ → ℂ × (ℝ → ℝ)) (q : ℂ) : ℝ → ℂ := chartPt q (ch q).1 (ch q).2

/-- The successive base points of the walk. -/
def walkPt (ch : ℂ → ℂ × (ℝ → ℝ)) (ℓ : ℝ) (p₀ : ℂ) : ℕ → ℂ
  | 0 => p₀
  | n + 1 => stepCurve ch (walkPt ch ℓ p₀ n) ℓ

/-- The boundary walk. -/
def walk (ch : ℂ → ℂ × (ℝ → ℝ)) (ℓ : ℝ) (p₀ : ℂ) (t : ℝ) : ℂ :=
  stepCurve ch (walkPt ch ℓ p₀ ⌊t / ℓ⌋₊) (t - ⌊t / ℓ⌋₊ * ℓ)

section Walk

variable {Ω : Set ℂ} {ρ H : ℝ} {K : NNReal} {ch : ℂ → ℂ × (ℝ → ℝ)} {ℓ : ℝ} {p₀ : ℂ}

/-- Standing hypotheses on the walk data. -/
structure WalkData (Ω : Set ℂ) (ρ H : ℝ) (K : NNReal) (ch : ℂ → ℂ × (ℝ → ℝ)) (ℓ : ℝ)
    (p₀ : ℂ) : Prop where
  isOpen : IsOpen Ω
  chart : ∀ p ∈ frontier Ω, IsChartAt Ω p (ch p).1 ρ H K (ch p).2
  ℓ_pos : 0 < ℓ
  ℓ_lt : ℓ < ρ
  p₀_mem : p₀ ∈ frontier Ω

lemma WalkData.stepCurve_mem (hw : WalkData Ω ρ H K ch ℓ p₀) {q : ℂ} (hq : q ∈ frontier Ω)
    {x : ℝ} (hx : |x| < ρ) : stepCurve ch q x ∈ frontier Ω :=
  chartPt_mem_frontier hw.isOpen (hw.chart q hq) hx

lemma WalkData.walkPt_mem (hw : WalkData Ω ρ H K ch ℓ p₀) (n : ℕ) :
    walkPt ch ℓ p₀ n ∈ frontier Ω := by
  induction n with
  | zero => exact hw.p₀_mem
  | succ n ih =>
    exact hw.stepCurve_mem ih (by rw [abs_of_pos hw.ℓ_pos]; exact hw.ℓ_lt)

lemma WalkData.stepCurve_zero (hw : WalkData Ω ρ H K ch ℓ p₀) {q : ℂ} (hq : q ∈ frontier Ω) :
    stepCurve ch q 0 = q :=
  chartPt_zero (hw.chart q hq).2.2.2.2.1

lemma WalkData.lipschitz_stepCurve (hw : WalkData Ω ρ H K ch ℓ p₀) {q : ℂ}
    (hq : q ∈ frontier Ω) : LipschitzWith (1 + K) (stepCurve ch q) :=
  lipschitzWith_chartPt (hw.chart q hq).1 (hw.chart q hq).2.2.2.1

/-- On the `n`-th step, the walk follows the `n`-th chart graph. -/
lemma WalkData.walk_eq (hw : WalkData Ω ρ H K ch ℓ p₀) (n : ℕ) {u : ℝ} (hu : u ∈ Icc 0 ℓ) :
    walk ch ℓ p₀ (n * ℓ + u) = stepCurve ch (walkPt ch ℓ p₀ n) u := by
  have hℓ := hw.ℓ_pos
  rcases lt_or_eq_of_le hu.2 with hlt | heq
  · have hfl : ⌊(n * ℓ + u) / ℓ⌋₊ = n := by
      rw [Nat.floor_eq_iff (by have := hu.1; positivity)]
      constructor
      · rw [le_div_iff₀ hℓ]; linarith [hu.1]
      · rw [div_lt_iff₀ hℓ]; linarith
    simp only [walk, hfl]; congr 1; ring
  · rw [heq]
    have hfl : ⌊(n * ℓ + ℓ) / ℓ⌋₊ = n + 1 := by
      rw [show ((n : ℝ) * ℓ + ℓ) / ℓ = ((n + 1 : ℕ) : ℝ) by push_cast; field_simp]
      exact Nat.floor_natCast _
    simp only [walk, hfl]
    have : (n : ℝ) * ℓ + ℓ - ((n + 1 : ℕ) : ℝ) * ℓ = 0 := by push_cast; ring
    rw [this, hw.stepCurve_zero (hw.walkPt_mem _)]
    rfl

/-- Before the first full step (including negative times), the walk is the first chart graph. -/
lemma WalkData.walk_eq_of_le (hw : WalkData Ω ρ H K ch ℓ p₀) {t : ℝ} (ht : t ≤ ℓ) :
    walk ch ℓ p₀ t = stepCurve ch p₀ t := by
  have hℓ := hw.ℓ_pos
  rcases le_or_gt 0 t with h0 | h0
  · have := hw.walk_eq 0 ⟨h0, ht⟩
    simpa [walkPt] using this
  · have hfl : ⌊t / ℓ⌋₊ = 0 := Nat.floor_eq_zero.mpr (by
      have : t / ℓ < 0 := div_neg_of_neg_of_pos h0 hℓ
      linarith)
    simp [walk, hfl, walkPt]

lemma WalkData.lipschitzWith_walk (hw : WalkData Ω ρ H K ch ℓ p₀) :
    LipschitzWith (1 + K) (walk ch ℓ p₀) := by
  refine lipschitzWith_of_pieces hw.ℓ_pos fun n => ?_
  rcases lt_or_ge n 0 with hn | hn
  · -- negative pieces: the first chart graph
    have hsub : Icc ((n : ℝ) * ℓ) ((n + 1) * ℓ) ⊆ Iic ℓ := fun t ht => by
      have h1 : (n : ℝ) + 1 ≤ 0 := by exact_mod_cast hn
      have h2 := mul_le_mul_of_nonneg_right h1 hw.ℓ_pos.le
      have := ht.2; simp only [mem_Iic]; nlinarith [hw.ℓ_pos]
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [hw.walk_eq_of_le (hsub hx), hw.walk_eq_of_le (hsub hy)]
    exact (hw.lipschitz_stepCurve hw.p₀_mem).dist_le_mul x y
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hwm : ∀ t ∈ Icc ((m : ℝ) * ℓ) ((m + 1) * ℓ),
        walk ch ℓ p₀ t = stepCurve ch (walkPt ch ℓ p₀ m) (t - m * ℓ) := fun t ht => by
      have := hw.walk_eq m (u := t - m * ℓ) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      simpa only [add_sub_cancel] using this
    push_cast
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [hwm x hx, hwm y hy]
    have := (hw.lipschitz_stepCurve (hw.walkPt_mem m)).dist_le_mul (x - m * ℓ) (y - m * ℓ)
    rwa [Real.dist_eq, sub_sub_sub_cancel_right, ← Real.dist_eq] at this

lemma WalkData.continuous_walk (hw : WalkData Ω ρ H K ch ℓ p₀) :
    Continuous (walk ch ℓ p₀) :=
  hw.lipschitzWith_walk.continuous

/-- The walk stays on the boundary (for `t > -ρ`). -/
lemma WalkData.walk_mem_frontier (hw : WalkData Ω ρ H K ch ℓ p₀) {t : ℝ} (ht : -ρ < t) :
    walk ch ℓ p₀ t ∈ frontier Ω := by
  have hℓ := hw.ℓ_pos
  rcases lt_or_ge t 0 with h0 | h0
  · rw [hw.walk_eq_of_le (by linarith)]
    exact hw.stepCurve_mem hw.p₀_mem (by rw [abs_lt]; constructor <;> linarith)
  · set n := ⌊t / ℓ⌋₊
    have h1 : (n : ℝ) ≤ t / ℓ := Nat.floor_le (by positivity)
    have h2 : t / ℓ < n + 1 := Nat.lt_floor_add_one _
    rw [le_div_iff₀ hℓ] at h1
    rw [div_lt_iff₀ hℓ] at h2
    have := hw.walk_eq n (u := t - n * ℓ) ⟨by linarith, by linarith⟩
    rw [add_sub_cancel] at this
    rw [this]
    exact hw.stepCurve_mem (hw.walkPt_mem n) (by rw [abs_lt]; constructor <;> linarith [hw.ℓ_lt])

/-- Abscissa of the walk in a chart. -/
def walkX (ch : ℂ → ℂ × (ℝ → ℝ)) (ℓ : ℝ) (p₀ : ℂ) (p c : ℂ) (s : ℝ) : ℝ :=
  (c * (walk ch ℓ p₀ s - p)).re

lemma WalkData.continuous_walkX (hw : WalkData Ω ρ H K ch ℓ p₀) (p c : ℂ) :
    Continuous (walkX ch ℓ p₀ p c) := by
  exact Complex.continuous_re.comp (continuous_const.mul (hw.continuous_walk.sub continuous_const))

/-- Where the walk follows a single chart graph, its abscissa in any other chart is locally
strictly increasing. -/
lemma WalkData.strictMonoOn_of_follow (hw : WalkData Ω ρ H K ch ℓ p₀) {q : ℂ}
    (hq : q ∈ frontier Ω) {a x₀ : ℝ} (hx₀ : |x₀| < ρ) {p c : ℂ} {r h : ℝ} {K' : NNReal}
    {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K' f) (hbox : stepCurve ch q x₀ ∈ chartBox p c r h) :
    ∃ ε > 0, ∀ S : Set ℝ, (∀ s ∈ S, walk ch ℓ p₀ s = stepCurve ch q (s - a)) →
      StrictMonoOn (walkX ch ℓ p₀ p c) (Icc (a + x₀ - ε) (a + x₀ + ε) ∩ S) := by
  obtain ⟨ε, hε, hmono⟩ := chart_orient hw.isOpen (hw.chart q hq) hch hx₀ hbox
  refine ⟨ε, hε, fun S hS s₁ hs₁ s₂ hs₂ h12 => ?_⟩
  simp only [walkX, hS s₁ hs₁.2, hS s₂ hs₂.2]
  exact hmono ⟨by linarith [hs₁.1.1], by linarith [hs₁.1.2]⟩
    ⟨by linarith [hs₂.1.1], by linarith [hs₂.1.2]⟩ (by linarith)

lemma WalkData.walk_eq_step' (hw : WalkData Ω ρ H K ch ℓ p₀) (n : ℕ) :
    ∀ s ∈ Icc ((n : ℝ) * ℓ) ((n + 1) * ℓ),
      walk ch ℓ p₀ s = stepCurve ch (walkPt ch ℓ p₀ n) (s - n * ℓ) := fun s hs => by
  have := hw.walk_eq n (u := s - n * ℓ) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simpa only [add_sub_cancel] using this

/-- **Local orientation of the walk.** In every chart whose box contains `walk t` (`t ≥ 0`),
the abscissa of the walk is strictly increasing near `t`. -/
theorem WalkData.walk_local_strictMono (hw : WalkData Ω ρ H K ch ℓ p₀) {t : ℝ} (ht : 0 ≤ t)
    {p c : ℂ} {r h : ℝ} {K' : NNReal} {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K' f)
    (hbox : walk ch ℓ p₀ t ∈ chartBox p c r h) :
    ∃ ε > 0, StrictMonoOn (walkX ch ℓ p₀ p c) (Icc (t - ε) (t + ε)) := by
  have hℓ := hw.ℓ_pos
  have hℓρ := hw.ℓ_lt
  set n := ⌊t / ℓ⌋₊ with hn
  have h1 : (n : ℝ) ≤ t / ℓ := Nat.floor_le (by positivity)
  have h2 : t / ℓ < n + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hℓ] at h1
  rw [div_lt_iff₀ hℓ] at h2
  set u := t - n * ℓ with hu
  have hu0 : 0 ≤ u := by linarith
  have huℓ : u < ℓ := by linarith
  have hwt : walk ch ℓ p₀ t = stepCurve ch (walkPt ch ℓ p₀ n) u :=
    hw.walk_eq_step' n t ⟨h1, by linarith⟩
  -- the right part (and the middle of a step)
  obtain ⟨εR, hεR, hR⟩ := hw.strictMonoOn_of_follow (hw.walkPt_mem n) (a := n * ℓ)
    (by rw [abs_of_nonneg hu0]; linarith) hch (by rw [← hwt]; exact hbox)
  have hRS := hR _ (hw.walk_eq_step' n)
  rcases lt_or_eq_of_le hu0 with hupos | hu0'
  · refine ⟨min εR (min u (ℓ - u)), lt_min hεR (lt_min hupos (by linarith)), ?_⟩
    refine hRS.mono fun s hs => ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have := min_le_left εR (min u (ℓ - u)); linarith [hs.1]
    · have := min_le_left εR (min u (ℓ - u)); linarith [hs.2]
    · have := le_trans (min_le_right εR _) (min_le_left u (ℓ - u)); linarith [hs.1]
    · have := le_trans (min_le_right εR _) (min_le_right u (ℓ - u)); linarith [hs.2]
  · -- at a step boundary `t = n ℓ`
    have htn : t = n * ℓ := by linarith
    have hRight : StrictMonoOn (walkX ch ℓ p₀ p c) (Icc t (t + min εR ℓ)) :=
      hRS.mono fun s hs => ⟨⟨by linarith [hs.1, hεR], by
        have := min_le_left εR ℓ; linarith [hs.2]⟩, by linarith [hs.1], by
        have := min_le_right εR ℓ; linarith [hs.2]⟩
    obtain ⟨εL, hεL, hLeft⟩ : ∃ εL > 0, StrictMonoOn (walkX ch ℓ p₀ p c) (Icc (t - εL) t) := by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · -- before the start: the first chart graph
        have ht0 : t = 0 := by rw [htn, hn0]; simp
        have hb0 : stepCurve ch p₀ 0 ∈ chartBox p c r h := by
          rw [← hw.walk_eq_of_le (by linarith), ← ht0]; exact hbox
        obtain ⟨ε', hε', h'⟩ := hw.strictMonoOn_of_follow hw.p₀_mem (a := 0)
          (by simp; linarith) hch hb0
        have h'' := h' (Iic ℓ) fun s hs => by rw [hw.walk_eq_of_le hs, sub_zero]
        refine ⟨ε', hε', h''.mono fun s hs => ⟨⟨?_, ?_⟩, ?_⟩⟩
        · rw [ht0] at hs; linarith [hs.1]
        · rw [ht0] at hs; linarith [hs.2]
        · rw [ht0] at hs; simp only [mem_Iic]; linarith [hs.2]
      · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hm] at htn
        have hwq : walk ch ℓ p₀ t = stepCurve ch (walkPt ch ℓ p₀ m) ℓ := by
          rw [htn]
          have := hw.walk_eq m (u := ℓ) ⟨hℓ.le, le_rfl⟩
          rw [← this]; push_cast; ring_nf
        obtain ⟨ε', hε', h'⟩ := hw.strictMonoOn_of_follow (hw.walkPt_mem m) (a := m * ℓ)
          (by rw [abs_of_pos hℓ]; exact hℓρ) hch (by rw [← hwq]; exact hbox)
        have h'' := h' _ (hw.walk_eq_step' m)
        refine ⟨min ε' ℓ, lt_min hε' hℓ, h''.mono fun s hs => ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
        · have := min_le_left ε' ℓ; push_cast at htn; linarith [hs.1]
        · push_cast at htn; linarith [hs.2, hε']
        · have := min_le_right ε' ℓ; push_cast at htn; linarith [hs.1]
        · push_cast at htn; linarith [hs.2]
    refine ⟨min εL (min εR ℓ), lt_min hεL (lt_min hεR hℓ), ?_⟩
    refine strictMonoOn_Icc_union (t := t) (hLeft.mono fun s hs => ⟨?_, hs.2⟩)
      (hRight.mono fun s hs => ⟨hs.1, ?_⟩)
    · have := min_le_left εL (min εR ℓ); linarith [hs.1]
    · have := min_le_right εL (min εR ℓ); linarith [hs.2]

/-- On an interval of nonnegative times along which the walk stays in a chart box, the abscissa
of the walk is strictly increasing. -/
theorem WalkData.strictMonoOn_walkX (hw : WalkData Ω ρ H K ch ℓ p₀) {α β : ℝ} (hα : 0 ≤ α)
    {p c : ℂ} {r h : ℝ} {K' : NNReal} {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K' f)
    (hbox : ∀ s ∈ Icc α β, walk ch ℓ p₀ s ∈ chartBox p c r h) :
    StrictMonoOn (walkX ch ℓ p₀ p c) (Icc α β) := by
  refine strictMonoOn_of_local_left (ordConnected_Icc) (hw.continuous_walkX p c).continuousOn
    fun y hy => ?_
  obtain ⟨ε, hε, hmono⟩ := hw.walk_local_strictMono (le_trans hα hy.1) hch (hbox y hy)
  exact ⟨ε, hε, fun y' _ h1 h2 => hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h2⟩

/-- **Capture.** If the walk stays in a chart box along `[α, β]`, every boundary point of the box
whose abscissa lies between those of `walk α` and `walk β` is on the walk. -/
theorem WalkData.capture (hw : WalkData Ω ρ H K ch ℓ p₀) {α β : ℝ} (hα : -ρ < α) (hαβ : α ≤ β)
    {p c : ℂ} {r h : ℝ} {K' : NNReal} {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K' f)
    (hbox : ∀ s ∈ Icc α β, walk ch ℓ p₀ s ∈ chartBox p c r h) {w : ℂ} (hwf : w ∈ frontier Ω)
    (hwb : w ∈ chartBox p c r h) (h1 : walkX ch ℓ p₀ p c α ≤ (c * (w - p)).re)
    (h2 : (c * (w - p)).re ≤ walkX ch ℓ p₀ p c β) :
    ∃ s ∈ Icc α β, walk ch ℓ p₀ s = w := by
  obtain ⟨s, hs, hsX⟩ := intermediate_value_Icc hαβ (hw.continuous_walkX p c).continuousOn
    ⟨h1, h2⟩
  exact ⟨s, hs, eq_of_frontier_of_re_eq hw.isOpen hch
    (hw.walk_mem_frontier (by linarith [hs.1])) hwf (hbox s hs) hwb hsX⟩

/-- Along one step, the walk moves at least as far as the elapsed time. -/
lemma WalkData.le_norm_walk_sub (hw : WalkData Ω ρ H K ch ℓ p₀) (n : ℕ) {u u' : ℝ}
    (hu : u ∈ Icc 0 ℓ) (hu' : u' ∈ Icc 0 ℓ) :
    |u' - u| ≤ ‖walk ch ℓ p₀ (n * ℓ + u') - walk ch ℓ p₀ (n * ℓ + u)‖ := by
  rw [hw.walk_eq n hu, hw.walk_eq n hu']
  have hc := (hw.chart _ (hw.walkPt_mem n)).1
  set q := walkPt ch ℓ p₀ n
  have := Complex.abs_re_le_norm ((ch q).1 * (stepCurve ch q u' - q) -
    (ch q).1 * (stepCurve ch q u - q))
  rw [Complex.sub_re, stepCurve, re_mul_chartPt_sub hc, re_mul_chartPt_sub hc, ← mul_sub,
    norm_mul, hc, one_mul, sub_sub_sub_cancel_right] at this
  exact this

end Walk

end PolyaNeumann
