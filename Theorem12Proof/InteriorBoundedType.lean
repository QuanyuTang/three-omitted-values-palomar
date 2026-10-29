module

public import Theorem12Proof.InteriorConstruction
public import Theorem12Proof.BoundedTypeUpper
import Mathlib.Tactic

/-!
# Non-bounded type of the interior construction

The actual upper-half-plane composite furnished by the construction is not a
quotient of bounded analytic functions. The global meromorphic continuation
is established separately in `FareyGlobalExtension`.
-/

@[expose] public section

open Complex UpperHalfPlane Metric Set NoWanderingDomains

namespace ThreeOmittedValues

theorem not_boundedType_of_all_divergent_fibres {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im})
    (hall : ∀ a : ℂ, a ≠ 0 → a ≠ 1 →
      ∃ (N : ℕ) (p : OrbitIndexFrom N → ℂ), Function.Injective p ∧
        (∀ i, 0 < (p i).im ∧ f (p i) = a) ∧
        ¬ Summable (fun i => blaschkeWeight (p i))) :
    ¬ IsBoundedTypeOnUpper f := by
  let a : ℂ := if f Complex.I = 2 then 3 else 2
  have ha0 : a ≠ 0 := by dsimp [a]; split_ifs <;> norm_num
  have ha1 : a ≠ 1 := by dsimp [a]; split_ifs <;> norm_num
  have hne : f Complex.I ≠ a := by
    dsimp [a]
    split_ifs with h
    · rw [h]
      norm_num
    · exact h
  obtain ⟨N, p, hp, hp_fibre, hp_div⟩ := hall a ha0 ha1
  apply not_boundedType_upper_of_nonsummable_fiber p hp hp_fibre hp_div
  exact ⟨Complex.I, by simp, hf Complex.I (by simp), hne⟩

theorem exists_interior_nonbounded_type_example :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → f z ≠ 0 ∧ f z ≠ 1) ∧
      (∀ a : ℂ, a ≠ 0 → a ≠ 1 →
        ∃ (N : ℕ) (p : OrbitIndexFrom N → ℂ), Function.Injective p ∧
          (∀ i, 0 < (p i).im ∧ f (p i) = a) ∧
          ¬ Summable (fun i => blaschkeWeight (p i))) ∧
      ¬ IsBoundedTypeOnUpper f := by
  obtain ⟨levels, Φ, _hlevels, _hbelow, _hvertices, _harcs, _hupper, _hΦ,
    _hΦinj, _hΦimage, _hΦcenter, hf, homits, hall, _e, _he, _he1⟩ :=
    exists_farey_map_with_all_divergent_interior_fibres
  let f : ℂ → ℂ := fun z => modularLambdaH (Φ z)
  have hf' : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im} :=
    hf.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_im)
  exact ⟨f, hf', homits, hall, not_boundedType_of_all_divergent_fibres hf' hall⟩

end ThreeOmittedValues
