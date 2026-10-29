module

public import Mathlib.Analysis.ConstantSpeed
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Arc-length reparametrization of a curve

These lemmas isolate the part of the rectifiable-boundary argument provided
by Mathlib's natural parametrization.  They do not assert that the Farey
boundary is rectifiable, nor that it is a Jordan curve.
-/

@[expose] public section

open Set

namespace ThreeOmittedValues

variable {f : ℝ → ℂ} {s : Set ℝ} {a : ℝ}

/-- On its natural parameter set, the arc-length parametrization is
1-Lipschitz. -/
theorem naturalParameterization_lipschitzOn_image
    (hf : LocallyBoundedVariationOn f s) (ha : a ∈ s) :
    LipschitzOnWith 1 (naturalParameterization f s a)
      (variationOnFromTo f s a '' s) := by
  let t := variationOnFromTo f s a '' s
  let g := naturalParameterization f s a
  have hg : HasUnitSpeedOn g t := has_unit_speed_naturalParameterization f hf ha
  have hord : ∀ ⦃u v : ℝ⦄, u ∈ t → v ∈ t → u ≤ v →
      dist (g u) (g v) ≤ dist u v := by
    intro u v hu hv huv
    have he := eVariationOn.edist_le g
      (s := t ∩ Icc u v) ⟨hu, le_rfl, huv⟩ ⟨hv, huv, le_rfl⟩
    have heq := hg hu hv
    change eVariationOn g (t ∩ Icc u v) = ENNReal.ofReal (1 * (v - u)) at heq
    rw [heq, edist_dist] at he
    simp only [one_mul] at he
    have hdist := (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr huv)).mp he
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huv), neg_sub]
    exact hdist
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  simp only [NNReal.coe_one, one_mul]
  rcases le_total x y with hxy | hyx
  · exact hord hx hy hxy
  · simpa only [dist_comm] using hord hy hx hyx

/-- Natural parametrization traces exactly the original curve on the image of
the signed variation map. -/
theorem naturalParameterization_image_eq
    (hf : LocallyBoundedVariationOn f s) (ha : a ∈ s) :
    naturalParameterization f s a '' (variationOnFromTo f s a '' s) = f '' s := by
  ext z
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨b, hb, ?_⟩
    exact (edist_eq_zero.mp (edist_naturalParameterization_eq_zero hf ha hb)).symm
  · rintro ⟨b, hb, rfl⟩
    refine ⟨variationOnFromTo f s a b, ⟨b, hb, rfl⟩, ?_⟩
    exact edist_eq_zero.mp (edist_naturalParameterization_eq_zero hf ha hb)

/-- For a continuous rectifiable curve, the cumulative length fills the
whole interval from zero to its total length. -/
theorem signedVariation_image_Icc {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hcont : ContinuousOn f (Icc a b)) :
    variationOnFromTo f (Icc a b) a '' Icc a b =
      Icc 0 (variationOnFromTo f (Icc a b) a b) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hc : ContinuousOn (variationOnFromTo f (Icc a b) a) (Icc a b) := by
    intro x hx
    exact (hf.continuousWithinAt_variationOnFromTo_iff ha hx).2 (hcont x hx)
  have hm := variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn ha
  simpa only [variationOnFromTo.self] using hc.image_Icc_of_monotoneOn hab hm

/-- Arc-length parametrization preserves injectivity on the half-open
parameter interval of a continuous rectifiable Jordan curve. -/
theorem naturalParameterization_injOn_Ico {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hcont : ContinuousOn f (Icc a b))
    (hinj : InjOn f (Ico a b)) :
    InjOn (naturalParameterization f (Icc a b) a)
      (Ico 0 (variationOnFromTo f (Icc a b) a b)) := by
  let V := variationOnFromTo f (Icc a b) a
  have hV : V '' Icc a b = Icc 0 (V b) := signedVariation_image_Icc hab hf hcont
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  intro x hx y hy heq
  have hx' : x ∈ V '' Icc a b := hV.symm ▸ ⟨hx.1, hx.2.le⟩
  have hy' : y ∈ V '' Icc a b := hV.symm ▸ ⟨hy.1, hy.2.le⟩
  obtain ⟨u, hu, rfl⟩ := hx'
  obtain ⟨v, hv, rfl⟩ := hy'
  have hu' : u ∈ Ico a b := ⟨hu.1, lt_of_le_of_ne hu.2 (by
    intro h; subst u; exact (lt_irrefl (V b)) hx.2)⟩
  have hv' : v ∈ Ico a b := ⟨hv.1, lt_of_le_of_ne hv.2 (by
    intro h; subst v; exact (lt_irrefl (V b)) hy.2)⟩
  have hgu : naturalParameterization f (Icc a b) a (V u) = f u :=
    edist_eq_zero.mp (edist_naturalParameterization_eq_zero hf.locallyBoundedVariationOn ha hu)
  have hgv : naturalParameterization f (Icc a b) a (V v) = f v :=
    edist_eq_zero.mp (edist_naturalParameterization_eq_zero hf.locallyBoundedVariationOn ha hv)
  have huv : u = v := hinj hu' hv' (hgu.symm.trans (heq.trans hgv))
  rw [huv]

/-- A continuous rectifiable Jordan loop can be traversed at unit speed by a
globally 1-Lipschitz map. The map is constant outside the traversal interval;
periodic extension is a separate step. -/
theorem exists_lipschitz_loop_of_rectifiable {a b : ℝ} (hab : a < b)
    (hf : BoundedVariationOn f (Icc a b)) (hcont : ContinuousOn f (Icc a b))
    (hclosed : f a = f b) (hinj : InjOn f (Ico a b)) :
    ∃ (Γ : ℝ → ℂ), LipschitzWith 1 Γ ∧ ∃ T : ℝ, 0 < T ∧ Γ T = Γ 0 ∧
      InjOn Γ (Ico 0 T) ∧ Γ '' Icc 0 T = f '' Icc a b := by
  let V := variationOnFromTo f (Icc a b) a
  let g := naturalParameterization f (Icc a b) a
  let T := V b
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hV : V '' Icc a b = Icc 0 T := signedVariation_image_Icc hab.le hf hcont
  have hzero : V a = 0 := variationOnFromTo.self f (Icc a b) a
  have hg (u : ℝ) (hu : u ∈ Icc a b) : g (V u) = f u :=
    edist_eq_zero.mp (edist_naturalParameterization_eq_zero hf.locallyBoundedVariationOn ha hu)
  have hT0 : 0 ≤ T := variationOnFromTo.nonneg_of_le f (Icc a b) hab.le
  have hT : 0 < T := by
    let m := (a + b) / 2
    have ham : a < m := by dsimp [m]; linarith
    have hmb : m < b := by dsimp [m]; linarith
    have hm : m ∈ Icc a b := ⟨ham.le, hmb.le⟩
    have hdiff : f a ≠ f m := by
      intro heq
      exact (ne_of_lt ham) (hinj ⟨le_rfl, hab⟩ ⟨ham.le, hmb⟩ heq)
    have hmV : V m ∈ Icc 0 T := hV ▸ ⟨m, hm, rfl⟩
    by_contra hn
    have hTzero : T = 0 := le_antisymm (le_of_not_gt hn) hT0
    have hmzero : V m = 0 := le_antisymm (hTzero ▸ hmV.2) hmV.1
    apply hdiff
    calc
      f a = g (V a) := (hg a ha).symm
      _ = g (V m) := by rw [hzero, hmzero]
      _ = f m := hg m hm
  let c : ℝ → ℝ := fun x => max 0 (min x T)
  have hc (x : ℝ) : c x ∈ Icc 0 T :=
    ⟨le_max_left _ _, max_le hT0 (min_le_right _ _)⟩
  have hceq (x : ℝ) (hx : x ∈ Icc 0 T) : c x = x := by
    dsimp [c]
    rw [min_eq_left hx.2, max_eq_right hx.1]
  have hcl : LipschitzWith 1 c := (LipschitzWith.id.min_const T).const_max 0
  have hgl : LipschitzOnWith 1 g (Icc 0 T) := by
    rw [← hV]
    exact naturalParameterization_lipschitzOn_image hf.locallyBoundedVariationOn ha
  let Γ : ℝ → ℂ := fun x => g (c x)
  have hΓ : LipschitzWith 1 Γ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 := hgl.dist_le_mul (c x) (hc x) (c y) (hc y)
    have h2 := hcl.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at h1 h2
    simpa only [NNReal.coe_one, one_mul, Γ] using h1.trans h2
  have hΓeq (x : ℝ) (hx : x ∈ Icc 0 T) : Γ x = g x := by
    simp only [Γ, hceq x hx]
  have hg0 : g 0 = f a := by simpa only [hzero] using hg a ha
  have hgT : g T = f b := hg b hb
  refine ⟨Γ, hΓ, T, hT, ?_, ?_, ?_⟩
  · rw [hΓeq T ⟨hT0, le_rfl⟩, hΓeq 0 ⟨le_rfl, hT0⟩, hgT, hg0, hclosed]
  · intro x hx y hy hxy
    rw [hΓeq x ⟨hx.1, hx.2.le⟩, hΓeq y ⟨hy.1, hy.2.le⟩] at hxy
    exact naturalParameterization_injOn_Ico hab.le hf hcont hinj hx hy hxy
  · calc
      Γ '' Icc 0 T = g '' Icc 0 T := Set.image_congr hΓeq
      _ = g '' (V '' Icc a b) := by rw [hV]
      _ = f '' Icc a b := naturalParameterization_image_eq hf.locallyBoundedVariationOn ha

end ThreeOmittedValues
