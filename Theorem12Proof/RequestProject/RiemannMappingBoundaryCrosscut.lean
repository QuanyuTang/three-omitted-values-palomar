module

public import Theorem12Proof.RequestProject.RiemannMappingBoundaryOscillation
public import Theorem12Proof.RequestProject.BoundaryConnected
public import Mathlib.Topology.Piecewise

/-!
# Actual short boundary arcs and small conformal cap loops

The inverse modulus of an actual periodic Jordan parametrization is
proved by compactness, rather than postulated for the physical boundary.
It closes every sufficiently small genuine conformal cap by an actual
short boundary arc. Coincident cap endpoints are treated separately.

These are constructions of small closed Jordan loops. The assertion
that the image of the entire source cap lies on their bounded side is a
separate planar separation statement, and is not an assumption here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

/-- A periodic Jordan parametrization has no repeated values at
parameters whose separation is strictly less than one period. -/
theorem jordanParam_eq_of_eq_of_abs_sub_lt {γ : ℝ → ℂ}
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : InjOn γ (Ico 0 (2 * Real.pi))) {x y : ℝ}
    (hxy : γ x = γ y) (hlt : |x - y| < 2 * Real.pi) : x = y := by
  have hmem : ∀ z, toIcoMod Real.two_pi_pos 0 z ∈ Ico 0 (2 * Real.pi) := fun z => by
    have h := toIcoMod_mem_Ico Real.two_pi_pos 0 z
    rwa [zero_add] at h
  have hval : ∀ z, γ (toIcoMod Real.two_pi_pos 0 z) = γ z := fun z => by
    rw [toIcoMod, hper.sub_zsmul_eq]
  have h := hinj (hmem x) (hmem y) (by rw [hval, hval, hxy])
  simp only [toIcoMod] at h
  let n := toIcoDiv Real.two_pi_pos 0 x
  let m := toIcoDiv Real.two_pi_pos 0 y
  have hd : x - y = ((n - m : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [zsmul_eq_mul, zsmul_eq_mul] at h
    push_cast
    dsimp [n, m]
    linarith
  have hk : n - m = 0 := by
    rw [hd, abs_mul, abs_of_pos Real.two_pi_pos] at hlt
    have h1 : |((n - m : ℤ) : ℝ)| < 1 := by
      by_contra hc
      push_neg at hc
      nlinarith [Real.two_pi_pos]
    rw [← Int.cast_abs] at h1
    have h2 : |n - m| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.mp h2
  rw [hk] at hd
  simp only [Int.cast_zero, zero_mul] at hd
  linarith

/-- The genuine inverse modulus, with the two possible short cyclic
directions retained. This includes the identified endpoints `0` and `2π`. -/
theorem jordanParam_uniform_cyclic_inverse {γ : ℝ → ℂ}
    (hc : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : InjOn γ (Ico 0 (2 * Real.pi))) {η : ℝ}
    (hη : 0 < η) (_hηπ : η < 2 * Real.pi) :
    ∃ δ > 0, ∀ s ∈ Icc 0 (2 * Real.pi), ∀ t ∈ Icc 0 (2 * Real.pi),
      ‖γ s - γ t‖ < δ → ∃ d : ℝ, |d| < η ∧ γ (s + d) = γ t := by
  let S : Set (ℝ × ℝ) :=
    (Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi)) ∩
      {p | η ≤ |p.1 - p.2| ∧ |p.1 - p.2| ≤ 2 * Real.pi - η}
  have hSc : IsCompact S := by
    apply (isCompact_Icc.prod isCompact_Icc).inter_right
    exact (isClosed_le continuous_const (continuous_fst.sub continuous_snd).abs).inter
      (isClosed_le (continuous_fst.sub continuous_snd).abs continuous_const)
  have hn : Continuous (fun p : ℝ × ℝ => ‖γ p.1 - γ p.2‖) :=
    ((hc.comp continuous_fst).sub (hc.comp continuous_snd)).norm
  have hpos : ∀ p ∈ S, 0 < ‖γ p.1 - γ p.2‖ := by
    intro p hp
    apply norm_pos_iff.mpr
    intro he
    have heq := jordanParam_eq_of_eq_of_abs_sub_lt hper hinj (sub_eq_zero.mp he)
      (lt_of_le_of_lt hp.2.2 (by linarith))
    have ha := hp.2.1
    rw [heq, sub_self, abs_zero] at ha
    linarith
  obtain ⟨δ, hδ, hbound⟩ : ∃ δ > 0, ∀ p ∈ S, δ ≤ ‖γ p.1 - γ p.2‖ := by
    rcases S.eq_empty_or_nonempty with he | hne
    · exact ⟨1, zero_lt_one, by simp [he]⟩
    · obtain ⟨p, hp, hmin⟩ := hSc.exists_isMinOn hne hn.continuousOn
      exact ⟨_, hpos p hp, fun q hq => hmin hq⟩
  refine ⟨δ, hδ, fun s hs t ht hst => ?_⟩
  have hshort : |s - t| < η ∨ 2 * Real.pi - |s - t| < η := by
    by_contra h
    push_neg at h
    have hbad : (s, t) ∈ S := ⟨⟨hs, ht⟩, h.1, by linarith [h.2]⟩
    exact (not_lt_of_ge (hbound _ hbad)) hst
  rcases hshort with h | h
  · refine ⟨t - s, ?_, by congr 1; ring⟩
    simpa only [abs_sub_comm] using h
  · by_cases hst' : s ≤ t
    · refine ⟨t - s - 2 * Real.pi, ?_, ?_⟩
      · rw [abs_sub_comm s t, abs_of_nonneg (sub_nonneg.mpr hst')] at h
        have hle : t - s ≤ 2 * Real.pi := by linarith [ht.2, hs.1]
        rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [show s + (t - s - 2 * Real.pi) = t - 2 * Real.pi by ring]
        exact hper.sub_eq t
    · have hts : t ≤ s := le_of_not_ge hst'
      refine ⟨t - s + 2 * Real.pi, ?_, ?_⟩
      · rw [abs_of_nonneg (sub_nonneg.mpr hts)] at h
        rw [abs_of_nonneg (by linarith [hs.2, ht.1])]
        linarith
      · rw [show s + (t - s + 2 * Real.pi) = t + 2 * Real.pi by ring]
        exact hper t

private theorem jordanParam_mem_image {γ : ℝ → ℂ}
    (hper : Function.Periodic γ (2 * Real.pi)) (s : ℝ) :
    γ s ∈ γ '' Icc 0 (2 * Real.pi) := by
  refine ⟨toIcoMod Real.two_pi_pos 0 s, ?_, ?_⟩
  · have h := toIcoMod_mem_Ico Real.two_pi_pos 0 s
    rw [zero_add] at h
    exact Ico_subset_Icc_self h
  · rw [toIcoMod, hper.sub_zsmul_eq]

/-- Nearby points on the actual physical Jordan boundary are joined by
an actual short Lipschitz boundary arc. When they differ, that arc is
injective on its entire closed parameter interval. -/
theorem jordanParam_exists_short_arc {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : InjOn γ (Ico 0 (2 * Real.pi))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ γ '' Icc 0 (2 * Real.pi), ∀ q ∈ γ '' Icc 0 (2 * Real.pi),
      ‖p - q‖ < δ → ∃ (A : ℝ → ℂ) (C : NNReal), LipschitzWith C A ∧
        A 0 = p ∧ A 1 = q ∧ MapsTo A (Icc 0 1) (γ '' Icc 0 (2 * Real.pi)) ∧
        (∀ u ∈ Icc 0 1, ∀ v ∈ Icc 0 1, ‖A u - A v‖ < ε) ∧
        (p ≠ q → InjOn A (Icc 0 1)) := by
  let η : ℝ := min Real.pi (ε / ((K : ℝ) + 1))
  have hη : 0 < η := lt_min Real.pi_pos (div_pos hε (by positivity))
  have hηπ : η < 2 * Real.pi :=
    (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  obtain ⟨δ, hδ, hmod⟩ := jordanParam_uniform_cyclic_inverse hK.continuous hper hinj hη hηπ
  refine ⟨δ, hδ, ?_⟩
  rintro p ⟨s, hs, hsp⟩ q ⟨t, ht, htq⟩ hpq
  obtain ⟨d, hd, hend⟩ := hmod s hs t ht (by simpa only [hsp, htq] using hpq)
  let A : ℝ → ℂ := fun u => γ (s + d * u)
  let C : NNReal := K * Real.toNNReal |d|
  have hAC : LipschitzWith C A := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    have h := hK.dist_le_mul (s + d * u) (s + d * v)
    simpa only [A, C, NNReal.coe_mul, Real.coe_toNNReal _ (abs_nonneg d),
      Real.dist_eq, show s + d * u - (s + d * v) = d * (u - v) by ring,
      abs_mul, mul_assoc] using h
  have hsmall : (K : ℝ) * |d| < ε := by
    have h1 : ((K : ℝ) + 1) * |d| < ((K : ℝ) + 1) * η :=
      mul_lt_mul_of_pos_left hd (by positivity)
    have h2 : ((K : ℝ) + 1) * η ≤ ε := by
      have h := min_le_right Real.pi (ε / ((K : ℝ) + 1))
      simpa only [mul_comm] using (le_div_iff₀ (by positivity)).mp h
    have h3 : (K : ℝ) * |d| ≤ ((K : ℝ) + 1) * |d| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg d)
    exact h3.trans_lt (h1.trans_le h2)
  have huv (u : ℝ) (hu : u ∈ Icc 0 1) (v : ℝ) (hv : v ∈ Icc 0 1) :
      |u - v| ≤ 1 := abs_le.2 ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
  refine ⟨A, C, hAC, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [A, mul_zero, add_zero] using hsp
  · simpa only [A, mul_one] using hend.trans htq
  · intro u _
    exact jordanParam_mem_image hper _
  · intro u hu v hv
    have h := hAC.dist_le_mul u v
    rw [dist_eq_norm, Real.dist_eq] at h
    have hC : (C : ℝ) = (K : ℝ) * |d| := by
      simp only [C, NNReal.coe_mul, Real.coe_toNNReal _ (abs_nonneg d)]
    rw [hC] at h
    exact (h.trans (mul_le_of_le_one_right (by positivity) (huv u hu v hv))).trans_lt hsmall
  · intro hpq u hu v hv heq
    have hd0 : d ≠ 0 := by
      intro he
      rw [he, add_zero, hsp, htq] at hend
      exact hpq hend
    have hdist : |(s + d * u) - (s + d * v)| < 2 * Real.pi := by
      rw [show (s + d * u) - (s + d * v) = d * (u - v) by ring, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg d) (huv u hu v hv)).trans_lt (hd.trans hηπ)
    have he := jordanParam_eq_of_eq_of_abs_sub_lt hper hinj heq hdist
    exact mul_left_cancel₀ hd0 (add_left_cancel he)

private theorem riemannMapping_image_isOpen (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) : IsOpen (F '' ball (0 : ℂ) 1) :=
  RiemannInterior.isOpen_image_of_injOn isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
    hF hinj Subset.rfl isOpen_ball

/-- The genuine cap is injective before its terminal endpoint, including
its first frontier endpoint. No distinction between the two endpoint
limits is assumed. -/
theorem riemannMapping_cap_injOn_Ico (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {ζ : ℂ} {r a b : ℝ}
    (hr : r ≠ 0) (hwidth : b - a ≤ 2 * Real.pi)
    (harc : MapsTo (circleMap ζ r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' ball (0 : ℂ) 1)) : InjOn G (Ico a b) := by
  have hopen := riemannMapping_image_isOpen F hF hinj
  have hnot : G a ∉ F '' ball (0 : ℂ) 1 := by
    rw [hopen.frontier_eq] at hGa
    exact hGa.2
  intro x hx y hy heq
  rcases eq_or_lt_of_le hx.1 with hxa | hxa
  · rcases eq_or_lt_of_le hy.1 with hya | hya
    · exact hxa.symm.trans hya
    · exfalso
      have hyi : y ∈ Ioo a b := ⟨hya, hy.2⟩
      apply hnot
      refine ⟨circleMap ζ r y, harc hyi, ?_⟩
      exact (hGeq hyi).symm.trans (heq.symm.trans (congrArg G hxa.symm))
  · rcases eq_or_lt_of_le hy.1 with hya | hya
    · exfalso
      have hxi : x ∈ Ioo a b := ⟨hxa, hx.2⟩
      apply hnot
      refine ⟨circleMap ζ r x, harc hxi, ?_⟩
      exact (hGeq hxi).symm.trans (heq.trans (congrArg G hya.symm))
    · have hxi : x ∈ Ioo a b := ⟨hxa, hx.2⟩
      have hyi : y ∈ Ioo a b := ⟨hya, hy.2⟩
      apply injOn_circleMap_of_abs_sub_le' hr hwidth hx hy
      apply hinj (harc hxi) (harc hyi)
      exact (hGeq hxi).symm.trans (heq.trans (hGeq hyi))

/-- When the two physical endpoints differ, the full closed cap is an
injective arc. The endpoint exclusion uses the actual open image. -/
theorem riemannMapping_cap_injOn_Icc (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {ζ : ℂ} {r a b : ℝ}
    (hr : r ≠ 0) (hwidth : b - a ≤ 2 * Real.pi)
    (harc : MapsTo (circleMap ζ r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' ball (0 : ℂ) 1))
    (hGb : G b ∈ frontier (F '' ball (0 : ℂ) 1)) (hab : G a ≠ G b) :
    InjOn G (Icc a b) := by
  have hopen := riemannMapping_image_isOpen F hF hinj
  have hnot : G b ∉ F '' ball (0 : ℂ) 1 := by
    rw [hopen.frontier_eq] at hGb
    exact hGb.2
  have hi := riemannMapping_cap_injOn_Ico F hF hinj hr hwidth harc hGeq hGa
  intro x hx y hy heq
  rcases lt_or_eq_of_le hx.2 with hxb | hxb
  · rcases lt_or_eq_of_le hy.2 with hyb | hyb
    · exact hi ⟨hx.1, hxb⟩ ⟨hy.1, hyb⟩ heq
    · rcases eq_or_lt_of_le hx.1 with hxa | hxa
      · exact False.elim (hab (by simpa only [← hxa, hyb] using heq))
      · exfalso
        apply hnot
        refine ⟨circleMap ζ r x, harc ⟨hxa, hxb⟩, ?_⟩
        exact (hGeq ⟨hxa, hxb⟩).symm.trans (heq.trans (congrArg G hyb))
  · rcases lt_or_eq_of_le hy.2 with hyb | hyb
    · rcases eq_or_lt_of_le hy.1 with hya | hya
      · exact False.elim (hab (by simpa only [hxb, ← hya] using heq.symm))
      · exfalso
        apply hnot
        refine ⟨circleMap ζ r y, harc ⟨hya, hyb⟩, ?_⟩
        exact (hGeq ⟨hya, hyb⟩).symm.trans (heq.symm.trans (congrArg G hxb))
    · exact hxb.trans hyb.symm

private def capBoundaryLoop (P A : ℝ → ℂ) (u : ℝ) : ℂ :=
  if u ≤ 1 then P u else A (u - 1)

private theorem capBoundaryLoop_continuous {P A : ℝ → ℂ}
    (hP : Continuous P) (hA : Continuous A) (hjoin : A 0 = P 1) :
    Continuous (capBoundaryLoop P A) := by
  apply hP.if (fun u hu => ?_) (hA.comp (continuous_id.sub continuous_const))
  have hu1 : u = 1 := by
    have h := frontier_Iic_subset (1 : ℝ) hu
    exact mem_singleton_iff.mp h
  change P u = A (u - 1)
  subst u
  simpa only [sub_self] using hjoin.symm

/-- Concatenating two actual injective arcs with disjoint interiors
produces a closed Jordan loop, with the final endpoint omitted. -/
private theorem capBoundaryLoop_injOn {P A : ℝ → ℂ}
    (hP : InjOn P (Icc 0 1)) (hA : InjOn A (Icc 0 1))
    (hjoin : A 0 = P 1) (hclose : A 1 = P 0)
    (hdisj : Disjoint (P '' Ioo 0 1) (A '' Icc 0 1)) :
    InjOn (capBoundaryLoop P A) (Ico 0 2) := by
  have hcross : ∀ u ∈ Icc 0 1, ∀ v ∈ Ioo 1 2, P u ≠ A (v - 1) := by
    intro u hu v hv he
    have hv' : v - 1 ∈ Icc 0 1 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · have h := hA (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hv'
        (hclose.trans (by simpa only [← hu0] using he))
      linarith [hv.2]
    · rcases lt_or_eq_of_le hu.2 with hu1 | hu1
      · exact Set.disjoint_left.mp hdisj (mem_image_of_mem P ⟨hu0, hu1⟩)
          ⟨v - 1, hv', he.symm⟩
      · have h := hA (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hv'
          (hjoin.trans (by simpa only [hu1] using he))
        linarith [hv.1]
  intro u hu v hv he
  by_cases hu1 : u ≤ 1
  · by_cases hv1 : v ≤ 1
    · simp only [capBoundaryLoop, if_pos hu1, if_pos hv1] at he
      exact hP ⟨hu.1, hu1⟩ ⟨hv.1, hv1⟩ he
    · simp only [capBoundaryLoop, if_pos hu1, if_neg hv1] at he
      exact False.elim (hcross u ⟨hu.1, hu1⟩ v ⟨lt_of_not_ge hv1, hv.2⟩ he)
  · by_cases hv1 : v ≤ 1
    · simp only [capBoundaryLoop, if_neg hu1, if_pos hv1] at he
      exact False.elim (hcross v ⟨hv.1, hv1⟩ u ⟨lt_of_not_ge hu1, hu.2⟩ he.symm)
    · simp only [capBoundaryLoop, if_neg hu1, if_neg hv1] at he
      have h := hA ⟨by linarith [lt_of_not_ge hu1], by linarith [hu.2]⟩
        ⟨by linarith [lt_of_not_ge hv1], by linarith [hv.2]⟩ he
      linarith

private theorem normalized_cap_image {G : ℝ → ℂ} {a b : ℝ} (hab : a < b) :
    (fun u : ℝ => G (a + (b - a) * u)) '' Icc 0 1 = G '' Icc a b := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨a + (b - a) * u, ⟨?_, ?_⟩, rfl⟩ <;>
      nlinarith [hu.1, hu.2]
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨(θ - a) / (b - a), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr hθ.1) (sub_pos.mpr hab).le
    · rw [div_le_one (sub_pos.mpr hab)]
      linarith [hθ.2]
    · change G (a + (b - a) * ((θ - a) / (b - a))) = G θ
      congr 1
      rw [mul_div_cancel₀ _ (sub_pos.mpr hab).ne']
      ring

private theorem normalized_cap_injOn_Ico {G : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hi : InjOn G (Ico a b)) :
    InjOn (fun u : ℝ => G (a + (b - a) * u)) (Ico 0 1) := by
  intro u hu v hv he
  have h := hi ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    ⟨by nlinarith [hv.1], by nlinarith [hv.2]⟩ he
  have h' := add_left_cancel h
  exact mul_left_cancel₀ (sub_pos.mpr hab).ne' h'

private theorem normalized_cap_injOn_Icc {G : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hi : InjOn G (Icc a b)) :
    InjOn (fun u : ℝ => G (a + (b - a) * u)) (Icc 0 1) := by
  intro u hu v hv he
  have h := hi ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    ⟨by nlinarith [hv.1], by nlinarith [hv.2]⟩ he
  exact mul_left_cancel₀ (sub_pos.mpr hab).ne' (add_left_cancel h)

/-- A closed Lipschitz loop lying in a genuine ball has zero winding at
every point outside that ball. The logarithm branch is constructed on
the actual loop, using the unit ball about `1` in the slit plane. -/
theorem windingNumber_eq_zero_of_image_ball {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * Real.pi) = γ 0)
    {p z : ℂ} {R : ℝ}
    (hball : ∀ θ ∈ Icc 0 (2 * Real.pi), ‖γ θ - p‖ < R)
    (hfar : R ≤ ‖p - z‖) : windingNumber γ z = 0 := by
  have hR : 0 < R := (norm_nonneg _).trans_lt (hball 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hdpos : 0 < ‖p - z‖ := hR.trans_le hfar
  have hd : p - z ≠ 0 := norm_pos_iff.mp hdpos
  have hslit : ∀ θ ∈ Icc 0 (2 * Real.pi),
      (p - z)⁻¹ * (γ θ - z) ∈ Complex.slitPlane := by
    intro θ hθ
    have hsmall : ‖(γ θ - p) / (p - z)‖ < 1 := by
      rw [norm_div]
      exact (div_lt_one hdpos).mpr ((hball θ hθ).trans_le hfar)
    have heq : (p - z)⁻¹ * (γ θ - z) = 1 + (γ θ - p) / (p - z) := by
      field_simp [hd]; ring
    rw [heq]
    exact Complex.mem_slitPlane_of_norm_lt_one hsmall
  have hi := integral_deriv_div_eq_log_sub hK Real.two_pi_pos.le (inv_ne_zero hd) hslit
  rw [hclosed, sub_self] at hi
  simp only [windingNumber, hi, mul_zero]

/-- Every sufficiently short genuine cap closes to an actual small
Jordan loop. Equal physical endpoint limits use the cap itself; distinct
limits use the proved short arc of the actual physical boundary.

The fixed interior value `F 0` is excluded from the constructed loop.
This theorem makes no assertion yet about which complementary component
contains the image of the whole source cap. -/
theorem riemannMapping_exists_small_cap_loop (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hγinj : InjOn γ (Ico 0 (2 * Real.pi)))
    (himage : γ '' Icc 0 (2 * Real.pi) = frontier (F '' ball (0 : ℂ) 1))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r : ℝ) (G Γ : ℝ → ℂ) (T : ℝ),
      0 < r ∧ r < δ ∧ r < 1 ∧ Continuous G ∧ Continuous Γ ∧
      (T = 1 ∨ T = 2) ∧ Γ T = Γ 0 ∧ InjOn Γ (Ico 0 T) ∧
      let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
      let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
      EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b) ∧
      G a ∈ frontier (F '' ball (0 : ℂ) 1) ∧
      G b ∈ frontier (F '' ball (0 : ℂ) 1) ∧ Γ 0 = G a ∧
      G '' Icc a b ⊆ Γ '' Icc 0 T ∧
      Γ '' Icc 0 T ⊆ G '' Icc a b ∪ frontier (F '' ball (0 : ℂ) 1) ∧
      (∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T, ‖Γ u - Γ v‖ < ε) ∧
      F 0 ∉ Γ '' Icc 0 T := by
  let Ω := F '' ball (0 : ℂ) 1
  have hopen : IsOpen Ω := riemannMapping_image_isOpen F hF hinj
  have hF0 : F 0 ∈ Ω := ⟨0, by simp, rfl⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen (F 0) hF0
  let e : ℝ := min ε (ρ / 2)
  have he : 0 < e := lt_min hε (half_pos hρ)
  obtain ⟨η, hη, hshort⟩ := jordanParam_exists_short_arc hK hper hγinj
    (show 0 < e / 3 by positivity)
  let ξ : ℝ := min (η / 2) (e / 3)
  have hξ : 0 < ξ := lt_min (half_pos hη) (by positivity)
  obtain ⟨r, G, hr, hrδ, hr1, hGc, hGeq, hGa, hGb, hdiam⟩ :=
    riemannMapping_exists_small_boundary_cap F hF hinj hb hζ hδ hξ
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  obtain ⟨hab, hwidth, harc, _, _⟩ := riemannCap_geometry hζ hr hr1
  have hwidth' : b - a ≤ 2 * Real.pi := by linarith
  have hGa' : G a ∉ Ω := by
    rw [hopen.frontier_eq] at hGa
    exact hGa.2
  have hcap : ∀ θ ∈ Icc a b, ‖G θ - G a‖ < e / 3 := by
    intro θ hθ
    exact (hdiam θ hθ a ⟨le_rfl, hab.le⟩).trans_le (min_le_right _ _)
  have havoid {Γ : ℝ → ℂ} {T : ℝ}
      (hsmall : ∀ u ∈ Icc 0 T, ‖Γ u - G a‖ < e / 3) : F 0 ∉ Γ '' Icc 0 T := by
    rintro ⟨u, hu, heq⟩
    apply hGa'
    apply hball
    rw [mem_ball, dist_eq_norm, norm_sub_rev]
    have h := hsmall u hu
    rw [heq] at h
    have heρ : e ≤ ρ / 2 := min_le_right _ _
    linarith
  have hpair {Γ : ℝ → ℂ} {T : ℝ}
      (hsmall : ∀ u ∈ Icc 0 T, ‖Γ u - G a‖ < e / 3) :
      ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T, ‖Γ u - Γ v‖ < ε := by
    intro u hu v hv
    have htri : ‖Γ u - Γ v‖ ≤ ‖Γ u - G a‖ + ‖Γ v - G a‖ := by
      have h := dist_triangle (Γ u) (G a) (Γ v)
      simpa only [dist_eq_norm, norm_sub_rev (G a) (Γ v)] using h
    have heε : e ≤ ε := min_le_left _ _
    linarith [hsmall u hu, hsmall v hv]
  let P : ℝ → ℂ := fun u => G (a + (b - a) * u)
  have hPc : Continuous P := hGc.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hP0 : P 0 = G a := by simp [P]
  have hP1 : P 1 = G b := by simp [P]
  have hPim : P '' Icc 0 1 = G '' Icc a b := normalized_cap_image hab
  have hPi : InjOn P (Ico 0 1) := normalized_cap_injOn_Ico hab
    (riemannMapping_cap_injOn_Ico F hF hinj hr.ne' hwidth' harc hGeq hGa)
  have hPsmall : ∀ u ∈ Icc 0 1, ‖P u - G a‖ < e / 3 := by
    intro u hu
    exact hcap (a + (b - a) * u) ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
  by_cases hend : G a = G b
  · refine ⟨r, G, P, 1, hr, hrδ, hr1, hGc, hPc, Or.inl rfl, ?_, hPi,
      hGeq, hGa, hGb, hP0, ?_, ?_, hpair hPsmall, havoid hPsmall⟩
    · rw [hP1, hP0]
      exact hend.symm
    · intro z hz
      rw [hPim]
      exact hz
    · rw [hPim]
      exact subset_union_left
  · have hnear : ‖G b - G a‖ < η := by
      have h := hdiam b ⟨hab.le, le_rfl⟩ a ⟨le_rfl, hab.le⟩
      have hξη : ξ ≤ η / 2 := min_le_left _ _
      linarith
    obtain ⟨A, C, hAC, hA0, hA1, hAm, hAd, hAi⟩ :=
      hshort (G b) (by simpa only [himage] using hGb)
        (G a) (by simpa only [himage] using hGa) hnear
    have hAfront : MapsTo A (Icc 0 1) (frontier Ω) := by simpa only [himage] using hAm
    have hAi' : InjOn A (Icc 0 1) := hAi (fun h => hend h.symm)
    have hPic : InjOn P (Icc 0 1) := normalized_cap_injOn_Icc hab
      (riemannMapping_cap_injOn_Icc F hF hinj hr.ne' hwidth' harc hGeq hGa hGb hend)
    have hdisj : Disjoint (P '' Ioo 0 1) (A '' Icc 0 1) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨u, hu, hPu⟩ ⟨v, hv, hAv⟩
      have huc : a + (b - a) * u ∈ Ioo a b :=
        ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
      have hzΩ : z ∈ Ω := by
        refine ⟨circleMap ζ r (a + (b - a) * u), harc huc, ?_⟩
        exact (hGeq huc).symm.trans hPu
      have hzfront : z ∈ frontier Ω := hAv ▸ hAfront hv
      rw [hopen.frontier_eq] at hzfront
      exact hzfront.2 hzΩ
    let Γ := capBoundaryLoop P A
    have hΓc : Continuous Γ := capBoundaryLoop_continuous hPc hAC.continuous
      (hA0.trans hP1.symm)
    have hΓ0 : Γ 0 = G a := by
      simp only [Γ, capBoundaryLoop, if_pos (by norm_num : (0 : ℝ) ≤ 1), hP0]
    have hΓclose : Γ 2 = Γ 0 := by
      simp only [Γ, capBoundaryLoop, if_neg (by norm_num : ¬(2 : ℝ) ≤ 1),
        if_pos (by norm_num : (0 : ℝ) ≤ 1), show (2 : ℝ) - 1 = 1 by norm_num, hA1, hP0]
    have hΓi : InjOn Γ (Ico 0 2) := capBoundaryLoop_injOn hPic hAi'
      (hA0.trans hP1.symm) (hA1.trans hP0.symm) hdisj
    have hΓsmall : ∀ u ∈ Icc 0 2, ‖Γ u - G a‖ < e / 3 := by
      intro u hu
      by_cases hu1 : u ≤ 1
      · simp only [Γ, capBoundaryLoop, if_pos hu1]
        exact hPsmall u ⟨hu.1, hu1⟩
      · simp only [Γ, capBoundaryLoop, if_neg hu1]
        rw [← hA1]
        exact hAd (u - 1) ⟨by linarith [lt_of_not_ge hu1], by linarith [hu.2]⟩
          1 (by norm_num)
    refine ⟨r, G, Γ, 2, hr, hrδ, hr1, hGc, hΓc, Or.inr rfl, hΓclose, hΓi,
      hGeq, hGa, hGb, hΓ0, ?_, ?_, hpair hΓsmall, havoid hΓsmall⟩
    · rw [← hPim]
      rintro z ⟨u, hu, hPu⟩
      refine ⟨u, ⟨hu.1, hu.2.trans (by norm_num)⟩, ?_⟩
      simpa only [Γ, capBoundaryLoop, if_pos hu.2] using hPu
    · rintro z ⟨u, hu, hΓu⟩
      by_cases hu1 : u ≤ 1
      · left
        rw [← hPim]
        exact ⟨u, ⟨hu.1, hu1⟩, by simpa only [Γ, capBoundaryLoop, if_pos hu1] using hΓu⟩
      · right
        have huf : A (u - 1) ∈ frontier Ω :=
          hAfront ⟨by linarith [lt_of_not_ge hu1], by linarith [hu.2]⟩
        have heq : A (u - 1) = z := by
          simpa only [Γ, capBoundaryLoop, if_neg hu1] using hΓu
        exact heq ▸ huf

/-- The same actual loop construction from the original simply
connected bounded Lipschitz domain. Its physical Jordan boundary data
are supplied by the proved boundary theorem, with no boundary extension
of the interior conformal map assumed. -/
theorem riemannMapping_exists_small_cap_loop_of_simplyConnected
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r : ℝ) (G Γ : ℝ → ℂ) (T : ℝ),
      0 < r ∧ r < δ ∧ r < 1 ∧ Continuous G ∧ Continuous Γ ∧
      (T = 1 ∨ T = 2) ∧ Γ T = Γ 0 ∧ InjOn Γ (Ico 0 T) ∧
      let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
      let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
      EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b) ∧
      G a ∈ frontier Ω ∧ G b ∈ frontier Ω ∧ Γ 0 = G a ∧
      G '' Icc a b ⊆ Γ '' Icc 0 T ∧
      Γ '' Icc 0 T ⊆ G '' Icc a b ∪ frontier Ω ∧
      (∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T, ‖Γ u - Γ v‖ < ε) ∧
      F 0 ∉ Γ '' Icc 0 T := by
  obtain ⟨γ, ⟨K, hK⟩, hper, hγinj, hγimage⟩ :=
    exists_jordanParam_of_isPreconnected_frontier hb hL
      (isPreconnected_frontier_of_simplyConnected hb hL hsc)
  have hbF : Bornology.IsBounded (F '' ball (0 : ℂ) 1) := himage.symm ▸ hb
  have hγF : γ '' Icc 0 (2 * Real.pi) = frontier (F '' ball (0 : ℂ) 1) := by
    simpa only [himage] using hγimage
  simpa only [himage] using riemannMapping_exists_small_cap_loop F hF hinj hbF
    hK hper hγinj hγF hζ hδ hε

end PolyaNeumann

end
