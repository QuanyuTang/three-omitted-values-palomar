module

public import Theorem12Proof.RequestProject.JordanWinding

/-!
# Lipschitz charts of a planar boundary

Basic facts about the Lipschitz charts of a Lipschitz domain `Ω ⊂ ℂ`:

* graph points of a chart are boundary points (`chartPt_mem_frontier`), and boundary points in a
  chart box are graph points (`eq_chartPt_of_frontier`);
* recentering of a chart at a nearby boundary point (`isChartAt_recenter`) and uniform charts
  for bounded Lipschitz domains (`exists_uniform_charts`);
* a continuous function that is "strictly increasing from the left" at every point of an interval
  is strictly increasing (`strictMonoOn_of_local_left`);
* **consistency of orientation** (`chart_orient`): along the boundary, the abscissa of one chart
  is a strictly increasing function of the abscissa of any other chart (the domain lies on the
  left in both).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- A Lipschitz chart of `Ω` at `p`: after the rigid motion `w ↦ c (w - p)`, inside the box
`|x| < r`, `|y| < h`, the domain is the region above the graph of the `K`-Lipschitz function `f`
(with `f 0 = 0`, and the graph over `|x| < r` inside the box). -/
def IsChartAt (Ω : Set ℂ) (p c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ) : Prop :=
  ‖c‖ = 1 ∧ 0 < r ∧ 0 < h ∧ LipschitzWith K f ∧ f 0 = 0 ∧ (∀ x : ℝ, |x| < r → |f x| < h) ∧
    ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im)

lemma IsLipschitzDomain.exists_chart {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) {p : ℂ}
    (hp : p ∈ frontier Ω) : ∃ (c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ),
      IsChartAt Ω p c r h K f :=
  hL.2 p hp

/-- The graph point of a chart with abscissa `x`. -/
def chartPt (p c : ℂ) (f : ℝ → ℝ) (x : ℝ) : ℂ := p + conj c * ((x : ℂ) + (f x : ℂ) * Complex.I)

lemma mul_chartPt_sub {p c : ℂ} (hc : ‖c‖ = 1) (f : ℝ → ℝ) (x : ℝ) :
    c * (chartPt p c f x - p) = (x : ℂ) + (f x : ℂ) * Complex.I := by
  have : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  simp only [chartPt, add_sub_cancel_left, ← mul_assoc, this, one_mul]

lemma re_mul_chartPt_sub {p c : ℂ} (hc : ‖c‖ = 1) (f : ℝ → ℝ) (x : ℝ) :
    (c * (chartPt p c f x - p)).re = x := by
  rw [mul_chartPt_sub hc]; simp

lemma im_mul_chartPt_sub {p c : ℂ} (hc : ‖c‖ = 1) (f : ℝ → ℝ) (x : ℝ) :
    (c * (chartPt p c f x - p)).im = f x := by
  rw [mul_chartPt_sub hc]; simp

lemma chartPt_zero {p c : ℂ} {f : ℝ → ℝ} (hf0 : f 0 = 0) : chartPt p c f 0 = p := by
  simp [chartPt, hf0]

lemma norm_mul_sub {c : ℂ} (hc : ‖c‖ = 1) (w p : ℂ) : ‖c * (w - p)‖ = ‖w - p‖ := by
  rw [norm_mul, hc, one_mul]

/-- A point is determined by its chart coordinates. -/
lemma eq_of_mul_sub_eq {c p w w' : ℂ} (hc : ‖c‖ = 1) (h : c * (w - p) = c * (w' - p)) :
    w = w' := by
  have hc0 : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hc; exact zero_ne_one hc
  have := mul_left_cancel₀ hc0 h
  linear_combination this

lemma eq_of_re_im_eq {c p w w' : ℂ} (hc : ‖c‖ = 1) (hre : (c * (w - p)).re = (c * (w' - p)).re)
    (him : (c * (w - p)).im = (c * (w' - p)).im) : w = w' :=
  eq_of_mul_sub_eq hc (Complex.ext hre him)

/-- The graph map of a chart is `(1 + K)`-Lipschitz. -/
lemma lipschitzWith_chartPt {p c : ℂ} (hc : ‖c‖ = 1) {K : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) : LipschitzWith (1 + K) (chartPt p c f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hcc : ‖conj c‖ = 1 := by rw [Complex.norm_conj, hc]
  simp only [chartPt, dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, hcc, one_mul]
  have h1 : ‖((x : ℂ) + (f x : ℂ) * Complex.I) - ((y : ℂ) + (f y : ℂ) * Complex.I)‖ ≤
      ‖((x - y : ℝ) : ℂ)‖ + ‖((f x - f y : ℝ) : ℂ) * Complex.I‖ := by
    have : ((x : ℂ) + (f x : ℂ) * Complex.I) - ((y : ℂ) + (f y : ℂ) * Complex.I) =
        ((x - y : ℝ) : ℂ) + ((f x - f y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this]; exact norm_add_le _ _
  have h2 : |f x - f y| ≤ K * |x - y| := by
    have := hf.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at h1
  push_cast
  rw [Real.norm_eq_abs]
  nlinarith

lemma continuous_chartPt {p c : ℂ} {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (chartPt p c f) := by
  unfold chartPt; fun_prop

/-- The open chart box. -/
def chartBox (p c : ℂ) (r h : ℝ) : Set ℂ :=
  {w | |(c * (w - p)).re| < r ∧ |(c * (w - p)).im| < h}

lemma isOpen_chartBox (p c : ℂ) (r h : ℝ) : IsOpen (chartBox p c r h) := by
  have hg : Continuous fun w : ℂ => c * (w - p) := by fun_prop
  exact (isOpen_lt (Complex.continuous_re.comp hg).abs continuous_const).inter
    (isOpen_lt (Complex.continuous_im.comp hg).abs continuous_const)

/-- A ball around the centre inside the box. -/
lemma ball_subset_chartBox {p c : ℂ} (hc : ‖c‖ = 1) {r h : ℝ} :
    ball p (min r h) ⊆ chartBox p c r h := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  have hn := norm_mul_sub hc w p
  refine ⟨lt_of_le_of_lt (Complex.abs_re_le_norm _) ?_,
    lt_of_le_of_lt (Complex.abs_im_le_norm _) ?_⟩
  · rw [hn]; exact lt_of_lt_of_le hw (min_le_left _ _)
  · rw [hn]; exact lt_of_lt_of_le hw (min_le_right _ _)

/-- Graph points of a chart are boundary points. -/
lemma chartPt_mem_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω) {p c : ℂ} {r h : ℝ} {K : NNReal}
    {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K f) {x : ℝ} (hx : |x| < r) :
    chartPt p c f x ∈ frontier Ω := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  rw [hΩo.frontier_eq]
  have hfx := hfb x hx
  refine ⟨?_, ?_⟩
  · -- limit of points above the graph
    rw [mem_closure_iff_nhds]
    intro U hU
    have hcont : Continuous fun s : ℝ => chartPt p c f x + (s : ℂ) * (conj c * Complex.I) := by
      fun_prop
    have ht : Tendsto (fun s : ℝ => chartPt p c f x + (s : ℂ) * (conj c * Complex.I))
        (𝓝[>] 0) (𝓝 (chartPt p c f x)) := by
      have := hcont.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < h - |f x| := by
      have : (0 : ℝ) < h - |f x| := by linarith
      exact eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds this)
    have hev : ∀ᶠ s : ℝ in 𝓝[>] 0, chartPt p c f x + (s : ℂ) * (conj c * Complex.I) ∈ U :=
      ht hU
    obtain ⟨s, hsU, hs, hspos⟩ := (hev.and (hsmall.and self_mem_nhdsWithin)).exists
    refine ⟨_, hsU, ?_⟩
    have hcc : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
    have hcoord : c * (chartPt p c f x + (s : ℂ) * (conj c * Complex.I) - p) =
        (x : ℂ) + ((f x + s : ℝ) : ℂ) * Complex.I := by
      have := mul_chartPt_sub (p := p) hc f x
      rw [add_sub_right_comm, mul_add, this]
      have h2 : c * ((s : ℂ) * (conj c * Complex.I)) = (s : ℂ) * Complex.I * (c * conj c) := by
        ring
      rw [h2, hcc]; push_cast; ring
    have hre : (c * (chartPt p c f x + (s : ℂ) * (conj c * Complex.I) - p)).re = x := by
      rw [hcoord]; simp
    have him : (c * (chartPt p c f x + (s : ℂ) * (conj c * Complex.I) - p)).im = f x + s := by
      rw [hcoord]; simp
    have hspos' : (0 : ℝ) < s := hspos
    have hfx' := abs_lt.mp hfx
    have habs : |f x + s| < h := by
      rw [abs_lt]; constructor
      · linarith
      · linarith [le_abs_self (f x)]
    refine (hΩ _ (by rw [hre]; exact hx) (by rw [him]; exact habs)).mpr ?_
    rw [hre, him]; linarith
  · intro hmem
    have := (hΩ _ (by rw [re_mul_chartPt_sub hc]; exact hx)
      (by rw [im_mul_chartPt_sub hc]; exact hfx)).mp hmem
    rw [re_mul_chartPt_sub hc, im_mul_chartPt_sub hc] at this
    exact lt_irrefl _ this

/-- Boundary points in a chart box are graph points. -/
lemma eq_chartPt_of_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω) {p c : ℂ} {r h : ℝ} {K : NNReal}
    {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K f) {w : ℂ} (hw : w ∈ frontier Ω)
    (hbox : w ∈ chartBox p c r h) : w = chartPt p c f (c * (w - p)).re := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  have hgr := chart_frontier_graph hΩo hf hΩ hw hbox.1 hbox.2
  refine eq_of_re_im_eq (p := p) hc ?_ ?_
  · rw [re_mul_chartPt_sub hc]
  · rw [im_mul_chartPt_sub hc, hgr]

/-- Two boundary points in a chart box with the same abscissa coincide. -/
lemma eq_of_frontier_of_re_eq {Ω : Set ℂ} (hΩo : IsOpen Ω) {p c : ℂ} {r h : ℝ} {K : NNReal}
    {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K f) {w w' : ℂ} (hw : w ∈ frontier Ω)
    (hw' : w' ∈ frontier Ω) (hbox : w ∈ chartBox p c r h) (hbox' : w' ∈ chartBox p c r h)
    (hre : (c * (w - p)).re = (c * (w' - p)).re) : w = w' := by
  rw [eq_chartPt_of_frontier hΩo hch hw hbox, eq_chartPt_of_frontier hΩo hch hw' hbox', hre]

/-- Along the boundary inside a chart box, distances are controlled by abscissae. -/
lemma norm_sub_le_of_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω) {p c : ℂ} {r h : ℝ} {K : NNReal}
    {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K f) {w w' : ℂ} (hw : w ∈ frontier Ω)
    (hw' : w' ∈ frontier Ω) (hbox : w ∈ chartBox p c r h) (hbox' : w' ∈ chartBox p c r h) :
    ‖w - w'‖ ≤ (1 + K) * |(c * (w - p)).re - (c * (w' - p)).re| := by
  have h1 := (lipschitzWith_chartPt (p := p) hch.1 hch.2.2.2.1).dist_le_mul
    (c * (w - p)).re (c * (w' - p)).re
  rw [← eq_chartPt_of_frontier hΩo hch hw hbox, ← eq_chartPt_of_frontier hΩo hch hw' hbox',
    dist_eq_norm, Real.dist_eq] at h1
  simpa using h1

/-! ### Recentering and uniform charts -/

/-- Recentering a chart at a boundary point of the half box. -/
lemma isChartAt_recenter {Ω : Set ℂ} (hΩo : IsOpen Ω) {p c : ℂ} {r h : ℝ} {K : NNReal}
    {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K f) {q : ℂ} (hq : q ∈ frontier Ω)
    (hqr : |(c * (q - p)).re| < r / 2) (hqh : |(c * (q - p)).im| < h / 2)
    {ρ H : ℝ} {K' : NNReal} (hρ : 0 < ρ) (hH : 0 < H) (hρr : ρ ≤ r / 2) (hHh : H ≤ h / 2)
    (hKK : K ≤ K') (hKρ : (K' : ℝ) * ρ < H) :
    IsChartAt Ω q c ρ H K'
      (fun x => f (x + (c * (q - p)).re) - f (c * (q - p)).re) := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  set X := (c * (q - p)).re with hX
  have hfK' : LipschitzWith K' f := hf.weaken hKK
  have hlip : LipschitzWith K' (fun x => f (x + X) - f X) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := hfK'.dist_le_mul (x + X) (y + X)
    simp only [Real.dist_eq, sub_sub_sub_cancel_right, add_sub_add_right_eq_sub] at this ⊢
    exact this
  refine ⟨hc, hρ, hH, hlip, by simp, fun x hx => ?_, fun w hw1 hw2 => ?_⟩
  · have := hlip.dist_le_mul x 0
    simp only [Real.dist_eq, sub_zero, zero_add, sub_self] at this
    calc |f (x + X) - f X| ≤ K' * |x| := this
      _ ≤ K' * ρ := mul_le_mul_of_nonneg_left hx.le K'.2
      _ < H := hKρ
  · have hY : (c * (q - p)).im = f X :=
      chart_frontier_graph hΩo hf hΩ hq (by linarith [hqr]) (by linarith [hqh])
    have hsplit : c * (w - p) = c * (w - q) + c * (q - p) := by ring
    have hre : (c * (w - p)).re = (c * (w - q)).re + X := by rw [hsplit, Complex.add_re]
    have him : (c * (w - p)).im = (c * (w - q)).im + f X := by
      rw [hsplit, Complex.add_im, hY]
    have h1 : |(c * (w - p)).re| < r := by
      rw [hre]; calc _ ≤ |(c * (w - q)).re| + |X| := abs_add_le _ _
        _ < r := by linarith
    have h2 : |(c * (w - p)).im| < h := by
      rw [him]; calc _ ≤ |(c * (w - q)).im| + |f X| := abs_add_le _ _
        _ < h := by rw [← hY]; linarith
    rw [hΩ w h1 h2, hre, him]
    constructor <;> intro hlt <;> linarith

lemma frontier_isCompact {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) : IsCompact (frontier Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)

/-- **Uniform charts.** A bounded Lipschitz domain has charts at every boundary point with
uniform size `ρ × H` and uniform Lipschitz constant `K`, with `K ρ < H`. -/
theorem exists_uniform_charts {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) :
    ∃ (ρ H : ℝ) (K : NNReal), 0 < ρ ∧ 0 < H ∧ (K : ℝ) * ρ < H ∧
      ∀ p ∈ frontier Ω, ∃ (c : ℂ) (f : ℝ → ℝ), IsChartAt Ω p c ρ H K f := by
  have hΩo := hL.1.1
  choose! c r h K f hch using fun p (hp : p ∈ frontier Ω) => hL.exists_chart hp
  set U : ℂ → Set ℂ := fun p => chartBox p (c p) (r p / 2) (h p / 2) with hU
  have hUo : ∀ p, IsOpen (U p) := fun p => isOpen_chartBox _ _ _ _
  have hcover : frontier Ω ⊆ ⋃ p ∈ frontier Ω, U p := fun q hq => by
    refine mem_biUnion hq ?_
    obtain ⟨-, hr, hh, -⟩ := hch q hq
    simp [hU, chartBox, hr, hh]
  obtain ⟨t, htΩ, htfin, hcov⟩ := (frontier_isCompact hb).elim_finite_subcover_image
    (fun p _ => hUo p) hcover
  by_cases hte : t.Nonempty
  swap
  · -- empty boundary: any constants work
    refine ⟨1, 2, 0, one_pos, two_pos, by norm_num, fun p hp => ?_⟩
    have := hcov hp
    rw [Set.not_nonempty_iff_eq_empty.mp hte] at this
    simp at this
  set Kt : NNReal := htfin.toFinset.sup' (by simpa using hte) K with hKt
  set Ht : ℝ := htfin.toFinset.inf' (by simpa using hte) (fun p => h p / 2) with hHt
  set Rt : ℝ := htfin.toFinset.inf' (by simpa using hte) (fun p => r p / 2) with hRt
  have hHt0 : 0 < Ht := by
    rw [hHt, Finset.lt_inf'_iff]
    intro p hp
    have := (hch p (htΩ (by simpa using hp))).2.2.1
    linarith
  have hRt0 : 0 < Rt := by
    rw [hRt, Finset.lt_inf'_iff]
    intro p hp
    have := (hch p (htΩ (by simpa using hp))).2.1
    linarith
  set ρ : ℝ := min Rt (Ht / (2 * (Kt + 1))) with hρ
  have hρ0 : 0 < ρ := lt_min hRt0 (by positivity)
  have hKρ : (Kt : ℝ) * ρ < Ht := by
    have h1 : ρ ≤ Ht / (2 * (Kt + 1)) := min_le_right _ _
    have hK0 : (0 : ℝ) ≤ Kt := Kt.2
    calc (Kt : ℝ) * ρ ≤ Kt * (Ht / (2 * (Kt + 1))) := mul_le_mul_of_nonneg_left h1 hK0
      _ < Ht := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
  refine ⟨ρ, Ht, Kt, hρ0, hHt0, hKρ, fun q hq => ?_⟩
  obtain ⟨p, hpt, hqU⟩ := mem_iUnion₂.mp (hcov hq)
  have hpt' : p ∈ htfin.toFinset := by simpa using hpt
  refine ⟨c p, _, isChartAt_recenter hΩo (hch p (htΩ hpt)) hq hqU.1 hqU.2 hρ0 hHt0
    (le_trans (min_le_left _ _) (Finset.inf'_le _ hpt')) (Finset.inf'_le _ hpt')
    (Finset.le_sup' K hpt') hKρ⟩

/-! ### Local monotonicity -/

/-- A continuous function on an order-connected set that is, at every point, strictly larger
than at all nearby points to the left, is strictly increasing. -/
lemma strictMonoOn_of_local_left {g : ℝ → ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    (hg : ContinuousOn g J)
    (hloc : ∀ y ∈ J, ∃ ε > 0, ∀ y' ∈ J, y - ε < y' → y' < y → g y' < g y) :
    StrictMonoOn g J := by
  intro y1 hy1 y2 hy2 h12
  have hsub : Icc y1 y2 ⊆ J := hJ.out hy1 hy2
  obtain ⟨m, hm, hmin⟩ := (isCompact_Icc (a := y1) (b := y2)).exists_isMinOn
    (nonempty_Icc.mpr h12.le) (hg.mono hsub)
  have key : ∀ m' ∈ Icc y1 y2, y1 < m' → ¬ IsMinOn g (Icc y1 y2) m' := by
    intro m' hm' hlt hmin'
    obtain ⟨ε, hε, hε'⟩ := hloc m' (hsub hm')
    set y' := max (m' - ε / 2) ((y1 + m') / 2)
    have hy'1 : y1 < y' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hy'2 : y' < m' := max_lt (by linarith) (by linarith)
    have hy'm : y' ∈ Icc y1 y2 := ⟨hy'1.le, by linarith [hm'.2]⟩
    have := hε' y' (hsub hy'm) (lt_of_lt_of_le (by linarith) (le_max_left _ _)) hy'2
    exact absurd (hmin' hy'm) (not_le.mpr this)
  have hm1 : m = y1 := by
    by_contra hne
    exact key m hm (lt_of_le_of_ne hm.1 (Ne.symm hne)) hmin
  subst hm1
  have hle : g m ≤ g y2 := hmin ⟨h12.le, le_rfl⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    refine key y2 ⟨h12.le, le_rfl⟩ h12 fun z hz => ?_
    rw [← heq]; exact hmin hz

/-- Mirror version: strictly smaller than at nearby points to the right gives strictly
decreasing. -/
lemma strictAntiOn_of_local_right {g : ℝ → ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    (hg : ContinuousOn g J)
    (hloc : ∀ y ∈ J, ∃ ε > 0, ∀ y' ∈ J, y < y' → y' < y + ε → g y' < g y) :
    StrictAntiOn g J := by
  have hJ' : (Neg.neg ⁻¹' J).OrdConnected := ⟨fun a ha b hb x hx => by
    simp only [Set.mem_preimage] at *
    exact hJ.out hb ha ⟨by linarith [hx.2], by linarith [hx.1]⟩⟩
  have hg' : ContinuousOn (fun y => g (-y)) (Neg.neg ⁻¹' J) :=
    hg.comp continuous_neg.continuousOn (fun y hy => hy)
  have hmono := strictMonoOn_of_local_left hJ' hg' fun y hy => by
    obtain ⟨ε, hε, h⟩ := hloc (-y) hy
    exact ⟨ε, hε, fun y' hy' h1 h2 => h (-y') hy' (by linarith) (by linarith)⟩
  intro a ha b hb hab
  have := hmono (show -b ∈ Neg.neg ⁻¹' J by simpa using hb)
    (show -a ∈ Neg.neg ⁻¹' J by simpa using ha) (by linarith)
  simpa using this

/-! ### Consistency of orientation -/

/-- **Orientation consistency.** Let `(p₁, c₁, f₁)` and `(p₂, c₂, f₂)` be two charts of `Ω`, and
let the chart-1 graph point with abscissa `x₀` lie in the chart-2 box. Then, near `x₀`, the
chart-2 abscissa of the chart-1 graph point is a strictly increasing function of `x₀`: both
charts traverse the boundary in the same direction (with `Ω` on the left). -/
theorem chart_orient {Ω : Set ℂ} (hΩo : IsOpen Ω) {p₁ c₁ p₂ c₂ : ℂ} {r₁ h₁ r₂ h₂ : ℝ}
    {K₁ K₂ : NNReal} {f₁ f₂ : ℝ → ℝ} (hch₁ : IsChartAt Ω p₁ c₁ r₁ h₁ K₁ f₁)
    (hch₂ : IsChartAt Ω p₂ c₂ r₂ h₂ K₂ f₂) {x₀ : ℝ} (hx₀ : |x₀| < r₁)
    (hbox : chartPt p₁ c₁ f₁ x₀ ∈ chartBox p₂ c₂ r₂ h₂) :
    ∃ ε > 0, StrictMonoOn (fun x => (c₂ * (chartPt p₁ c₁ f₁ x - p₂)).re)
      (Icc (x₀ - ε) (x₀ + ε)) := by
  obtain ⟨hc₁, hr₁, hh₁, hf₁, hf₁0, hfb₁, hΩ₁⟩ := hch₁
  obtain ⟨hc₂, hr₂, hh₂, hf₂, hf₂0, hfb₂, hΩ₂⟩ := hch₂
  set σ₁ := chartPt p₁ c₁ f₁ with hσ₁
  set σ₂ := chartPt p₂ c₂ f₂ with hσ₂
  have hσ₁c : Continuous σ₁ := continuous_chartPt hf₁.continuous
  have hσ₂c : Continuous σ₂ := continuous_chartPt hf₂.continuous
  -- a small closed interval around `x₀` on which everything is inside both boxes
  set O : Set ℝ := {x | |x| < r₁} ∩ σ₁ ⁻¹' chartBox p₂ c₂ r₂ h₂ with hO
  have hOo : IsOpen O := (isOpen_lt continuous_abs continuous_const).inter
    ((isOpen_chartBox _ _ _ _).preimage hσ₁c)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hOo x₀ ⟨hx₀, hbox⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  set I := Icc (x₀ - δ / 2) (x₀ + δ / 2) with hI
  have hIO : I ⊆ O := fun x hx => hball (by
    rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])
  set ψ : ℝ → ℝ := fun x => (c₂ * (σ₁ x - p₂)).re with hψ
  have hψc : Continuous ψ := by simp only [hψ]; fun_prop
  set J := ψ '' I with hJ
  have hJo : J.OrdConnected :=
    (isPreconnected_Icc.image ψ hψc.continuousOn).ordConnected
  have hfr : ∀ x ∈ I, σ₁ x ∈ frontier Ω := fun x hx =>
    chartPt_mem_frontier hΩo ⟨hc₁, hr₁, hh₁, hf₁, hf₁0, hfb₁, hΩ₁⟩ (hIO hx).1
  have hσeq : ∀ x ∈ I, σ₁ x = σ₂ (ψ x) := fun x hx =>
    eq_chartPt_of_frontier hΩo ⟨hc₂, hr₂, hh₂, hf₂, hf₂0, hfb₂, hΩ₂⟩ (hfr x hx) (hIO hx).2
  set φ : ℝ → ℝ := fun y => (c₁ * (σ₂ y - p₁)).re with hφ
  have hφψ : ∀ x ∈ I, φ (ψ x) = x := fun x hx => by
    simp only [hφ]; rw [← hσeq x hx, hσ₁, re_mul_chartPt_sub hc₁]
  set v : ℂ := c₂ * conj c₁ with hv
  set a := v.re
  set b := v.im
  have hab : a * a + b * b = 1 := by
    have h1 : ‖v‖ = 1 := by rw [hv, norm_mul, Complex.norm_conj, hc₁, hc₂, one_mul]
    have h2 := Complex.normSq_eq_norm_sq v
    rw [h1, Complex.normSq_apply] at h2
    linarith
  set C := (c₁ * (p₂ - p₁)).re with hC
  have hφform : ∀ y, φ y = a * y + b * f₂ y + C := fun y => by
    simp only [hφ, hσ₂, chartPt, hC]
    have : c₁ * (p₂ + conj c₂ * ((y : ℂ) + (f₂ y : ℂ) * Complex.I) - p₁) =
        conj v * ((y : ℂ) + (f₂ y : ℂ) * Complex.I) + c₁ * (p₂ - p₁) := by
      rw [hv, map_mul, Complex.conj_conj]; ring
    rw [this, Complex.add_re]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.ofReal_im]
    ring
  -- the key inequality: points above the chart-1 graph are in `Ω`
  have hkey : ∀ y ∈ J, ∀ᶠ s : ℝ in 𝓝[>] 0, f₂ (y - s * b) < f₂ y + s * a := by
    rintro y ⟨x, hx, rfl⟩
    have hcc₁ : c₁ * conj c₁ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc₁]; simp
    set e : ℂ := conj c₁ * Complex.I with he
    have hc1 : ∀ s : ℝ, c₁ * (σ₁ x + (s : ℂ) * e - p₁) =
        (x : ℂ) + ((f₁ x + s : ℝ) : ℂ) * Complex.I := fun s => by
      have := mul_chartPt_sub (p := p₁) hc₁ f₁ x
      rw [add_sub_right_comm, mul_add, hσ₁, this]
      have h2 : c₁ * ((s : ℂ) * e) = (s : ℂ) * Complex.I * (c₁ * conj c₁) := by
        rw [he]; ring
      rw [h2, hcc₁]; push_cast; ring
    have hc2 : ∀ s : ℝ, c₂ * (σ₁ x + (s : ℂ) * e - p₂) =
        c₂ * (σ₁ x - p₂) + (s : ℂ) * (v * Complex.I) := fun s => by
      rw [he, hv]; ring
    have hvI_re : (v * Complex.I).re = -b := Complex.mul_I_re v
    have hvI_im : (v * Complex.I).im = a := Complex.mul_I_im v
    have hgr : (c₂ * (σ₁ x - p₂)).im = f₂ (ψ x) := by
      have := congrArg (fun w => (c₂ * (w - p₂)).im) (hσeq x hx)
      rw [this, hσ₂, im_mul_chartPt_sub hc₂]
    -- eventually in the chart-2 box
    have hcont : Continuous fun s : ℝ => σ₁ x + (s : ℂ) * e := by fun_prop
    have hev2 : ∀ᶠ s : ℝ in 𝓝 0, σ₁ x + (s : ℂ) * e ∈ chartBox p₂ c₂ r₂ h₂ := by
      have := hcont.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
      exact this ((isOpen_chartBox _ _ _ _).mem_nhds (hIO hx).2)
    have hfx := hfb₁ x (hIO hx).1
    have hev1 : ∀ᶠ s : ℝ in 𝓝 0, s < h₁ - |f₁ x| :=
      eventually_lt_nhds (by linarith)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev2,
      eventually_nhdsWithin_of_eventually_nhds hev1, self_mem_nhdsWithin] with s hs2 hs1 hs0
    have hs0' : (0 : ℝ) < s := hs0
    have hmem : σ₁ x + (s : ℂ) * e ∈ Ω := by
      have hre : (c₁ * (σ₁ x + (s : ℂ) * e - p₁)).re = x := by rw [hc1]; simp
      have him : (c₁ * (σ₁ x + (s : ℂ) * e - p₁)).im = f₁ x + s := by rw [hc1]; simp
      have habs : |f₁ x + s| < h₁ := by
        rw [abs_lt]; constructor
        · linarith [(abs_lt.mp hfx).1]
        · linarith [le_abs_self (f₁ x)]
      refine (hΩ₁ _ (by rw [hre]; exact (hIO hx).1) (by rw [him]; exact habs)).mpr ?_
      rw [hre, him]; linarith
    have := (hΩ₂ _ hs2.1 hs2.2).mp hmem
    rw [hc2, Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
      hvI_re, hvI_im, hgr] at this
    have hψx : (c₂ * (σ₁ x - p₂)).re = ψ x := rfl
    rw [hψx] at this
    convert this using 2; ring
  have hev_eps : ∀ y ∈ J, ∃ ε > 0, ∀ s, 0 < s → s < ε → f₂ (y - s * b) < f₂ y + s * a :=
    fun y hy => by
      rcases (nhdsGT_basis (0:ℝ)).eventually_iff.mp (hkey y hy) with ⟨i, hi, h⟩
      exact ⟨i, hi, fun s h1 h2 => h ⟨h1, h2⟩⟩
  have hgc : ContinuousOn (fun y => f₂ y + a / b * y) J :=
    (hf₂.continuous.add (continuous_const.mul continuous_id)).continuousOn
  -- `φ` is strictly increasing on `J`
  have hφmono : StrictMonoOn φ J := by
    rcases lt_trichotomy b 0 with hb | hb | hb
    · have hb0 : b ≠ 0 := hb.ne
      have hanti : StrictAntiOn (fun y => f₂ y + a / b * y) J := by
        refine strictAntiOn_of_local_right hJo hgc fun y hy => ?_
        obtain ⟨ε, hε, h⟩ := hev_eps y hy
        refine ⟨ε * (-b), by nlinarith, fun y' _ h1 h2 => ?_⟩
        have hs := h ((y - y') / b) (div_pos_of_neg_of_neg (by linarith) hb)
          (by rw [div_lt_iff_of_neg hb]; linarith)
        have e1 : y - (y - y') / b * b = y' := by rw [div_mul_cancel₀ _ hb0]; ring
        rw [e1] at hs
        have e2 : (y - y') / b * a = a / b * y - a / b * y' := by ring
        rw [e2] at hs
        linarith
      intro y1 hy1 y2 hy2 h12
      have := hanti hy1 hy2 h12
      rw [hφform, hφform]
      simp only at this
      have hba : b * (a / b) = a := by field_simp
      have e : ∀ y, a * y + b * f₂ y + C = b * (f₂ y + a / b * y) + C := fun y => by
        rw [mul_add b, ← mul_assoc, hba]; ring
      rw [e, e]; nlinarith
    · have ha : a * a = 1 := by rw [hb] at hab; linarith
      obtain ⟨y₀, hy₀⟩ : J.Nonempty := (nonempty_Icc.mpr (by linarith)).image ψ
      obtain ⟨ε, hε, h⟩ := hev_eps y₀ hy₀
      have := h (ε / 2) (by positivity) (by linarith)
      rw [hb] at this
      simp only [mul_zero, sub_zero] at this
      have ha0 : 0 < a := by nlinarith
      have ha1 : a = 1 := by nlinarith
      intro y1 _ y2 _ h12
      rw [hφform, hφform, hb, ha1]; linarith
    · have hb0 : b ≠ 0 := hb.ne'
      have hmono : StrictMonoOn (fun y => f₂ y + a / b * y) J := by
        refine strictMonoOn_of_local_left hJo hgc fun y hy => ?_
        obtain ⟨ε, hε, h⟩ := hev_eps y hy
        refine ⟨ε * b, by positivity, fun y' _ h1 h2 => ?_⟩
        have hs := h ((y - y') / b) (div_pos (by linarith) hb)
          (by rw [div_lt_iff₀ hb]; linarith)
        have e1 : y - (y - y') / b * b = y' := by rw [div_mul_cancel₀ _ hb0]; ring
        rw [e1] at hs
        have e2 : (y - y') / b * a = a / b * y - a / b * y' := by ring
        rw [e2] at hs
        linarith
      intro y1 hy1 y2 hy2 h12
      have := hmono hy1 hy2 h12
      rw [hφform, hφform]
      simp only at this
      have hba : b * (a / b) = a := by field_simp
      have e : ∀ y, a * y + b * f₂ y + C = b * (f₂ y + a / b * y) + C := fun y => by
        rw [mul_add b, ← mul_assoc, hba]; ring
      rw [e, e]; nlinarith
  intro x hx x' hx' hxx'
  by_contra hle
  push_neg at hle
  have := hφmono.le_iff_le (mem_image_of_mem ψ hx') (mem_image_of_mem ψ hx) |>.mpr hle
  rw [hφψ x' hx', hφψ x hx] at this
  linarith

end PolyaNeumann
