module

public import Theorem12Proof.ClosedRealCurve
import Mathlib.Tactic

/-!
# A closed Jordan parametrization from an embedded real line

If the original curve is injective and avoids its common end limit, its
closed parametrization is injective on the half-open parameter interval.
-/

@[expose] public section

open Set

namespace ThreeOmittedValues

theorem closeRealCurve_injOn {G : ℝ → ℂ} {p : ℂ}
    (hG : Function.Injective G) (havoid : ∀ x, G x ≠ p) :
    InjOn (closeRealCurve G p) (Ico (-(Real.pi / 2)) (Real.pi / 2)) := by
  intro x hx y hy hxy
  by_cases hxa : x = -(Real.pi / 2)
  · subst x
    by_cases hya : y = -(Real.pi / 2)
    · exact hya.symm
    · have hyI : y ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨lt_of_le_of_ne hy.1 (Ne.symm hya), hy.2⟩
      have heq : p = G (Real.tan y) := by simpa [closeRealCurve, hyI] using hxy
      exact (havoid (Real.tan y) heq.symm).elim
  · have hxI : x ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), hx.2⟩
    by_cases hya : y = -(Real.pi / 2)
    · subst y
      have heq : G (Real.tan x) = p := by simpa [closeRealCurve, hxI] using hxy
      exact (havoid (Real.tan x) heq).elim
    · have hyI : y ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨lt_of_le_of_ne hy.1 (Ne.symm hya), hy.2⟩
      have heq : G (Real.tan x) = G (Real.tan y) := by
        simpa [closeRealCurve, hxI, hyI] using hxy
      exact Real.strictMonoOn_tan.injOn hxI hyI (hG heq)

theorem closeRealCurve_image (G : ℝ → ℂ) (p : ℂ) :
    closeRealCurve G p '' Icc (-(Real.pi / 2)) (Real.pi / 2) = insert p (Set.range G) := by
  have hab : -(Real.pi / 2) < Real.pi / 2 := by linarith [Real.pi_pos]
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [mem_insert_iff, mem_range]
    by_cases hI : t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)
    · right
      refine ⟨Real.tan t, ?_⟩
      simp [closeRealCurve, hI]
    · left
      simp [closeRealCurve, hI]
  · simp only [mem_insert_iff, mem_range]
    rintro (rfl | ⟨x, rfl⟩)
    · exact ⟨-(Real.pi / 2), ⟨le_rfl, hab.le⟩, by simp⟩
    · have hx := Real.arctan_mem_Ioo x
      refine ⟨Real.arctan x, ⟨hx.1.le, hx.2.le⟩, ?_⟩
      simp [closeRealCurve, hx]

end ThreeOmittedValues
