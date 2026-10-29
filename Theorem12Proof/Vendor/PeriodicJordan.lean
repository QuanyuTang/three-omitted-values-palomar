module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Periodic parametrization of a Lipschitz Jordan loop

The two proofs below are extracted from the prior Apache-2.0 Neumann
development, commit b37a190b8afc6efb128f204176d26deec8d88a8c, files
`RequestProject/BoundaryWalk.lean` and `RequestProject/BoundaryLoop.lean`.
They are placed in this namespace to avoid conflicts with the original.
-/

@[expose] public section
open Set Metric
open scoped Real
noncomputable section
namespace ThreeOmittedValues
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


end ThreeOmittedValues
end
