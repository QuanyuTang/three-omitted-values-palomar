module

public import Theorem12Proof.FareyGraphIdentification
import Mathlib.Tactic

/-!
# Local finiteness of the Farey vertices

On a finite Stern–Brocot chain, a zero of the height must be an endpoint of
one of its finitely many semicircles. Pasting the chains preserves local
finiteness of the zero set on the real line.
-/

@[expose] public section

open Metric Set

namespace ThreeOmittedValues

theorem finite_sternBrocot_zero_set (n : ℕ) :
    {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ chainHeight (sternBrocotEdges n) x = 0}.Finite := by
  classical
  let E : Finset ℝ := (sternBrocotEdges n).toFinset.image (fun e => endpointCoordinate e.left) ∪
    (sternBrocotEdges n).toFinset.image (fun e => endpointCoordinate e.right)
  apply E.finite_toSet.subset
  intro x hx
  obtain ⟨e, he, hl, hr⟩ := sternBrocotEdges_cover n hx.1.1 hx.1.2
  have hheight := sternBrocot_chainHeight_eq_edge n he hl hr
  have hedge : edgeHeight e x = 0 := by rw [← hheight]; exact hx.2
  have hsquare := edgeHeight_sq_of_inside e hl hr
  rw [hedge, zero_pow (by norm_num)] at hsquare
  rcases mul_eq_zero.mp hsquare.symm with hleft | hright
  · have heq : x = endpointCoordinate e.left := sub_eq_zero.mp hleft
    simp only [E, Finset.mem_coe, Finset.mem_union, Finset.mem_image, List.mem_toFinset]
    exact Or.inl ⟨e, he, heq.symm⟩
  · have heq : x = endpointCoordinate e.right := (sub_eq_zero.mp hright).symm
    simp only [E, Finset.mem_coe, Finset.mem_union, Finset.mem_image, List.mem_toFinset]
    exact Or.inr ⟨e, he, heq.symm⟩

theorem finite_pastedFarey_zeros_on_unit (levels : ℤ → ℕ) (n : ℤ) :
    (Icc (n : ℝ) ((n : ℝ) + 1) ∩ {x : ℝ | pastedFareyHeight levels x = 0}).Finite := by
  have hfin := (finite_sternBrocot_zero_set (levels n)).image (fun t : ℝ => t + (n : ℝ))
  apply hfin.subset
  intro x hx
  refine ⟨x - (n : ℝ), ?_, ?_⟩
  · constructor
    · constructor <;> linarith [hx.1.1, hx.1.2]
    · rw [← pastedFareyHeight_eq_on_unit levels n hx.1]
      exact hx.2
  · ring

theorem pastedFarey_zeros_locally_finite (levels : ℤ → ℕ) (x : ℝ) :
    (ball x 1 ∩ {y : ℝ | pastedFareyHeight levels y = 0}).Finite := by
  let n : ℤ := ⌊x⌋
  let Z : Set ℝ := {y : ℝ | pastedFareyHeight levels y = 0}
  let S₁ : Set ℝ := Icc ((n : ℝ) - 1) (n : ℝ) ∩ Z
  let S₂ : Set ℝ := Icc (n : ℝ) ((n : ℝ) + 1) ∩ Z
  let S₃ : Set ℝ := Icc ((n : ℝ) + 1) ((n : ℝ) + 2) ∩ Z
  have hS₁ : S₁.Finite := by
    simpa [S₁, Z] using finite_pastedFarey_zeros_on_unit levels (n - 1)
  have hS₂ : S₂.Finite := finite_pastedFarey_zeros_on_unit levels n
  have hS₃ : S₃.Finite := by
    simpa [S₃, Z, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using
      finite_pastedFarey_zeros_on_unit levels (n + 1)
  apply ((hS₁.union hS₂).union hS₃).subset
  intro y hy
  have hdist : |y - x| < 1 := by simpa [Real.dist_eq] using hy.1
  have hybounds := abs_lt.mp hdist
  have hxlo : (n : ℝ) ≤ x := Int.floor_le x
  have hxhi : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
  by_cases hy₁ : y ≤ (n : ℝ)
  · exact Or.inl (Or.inl ⟨⟨by linarith, hy₁⟩, hy.2⟩)
  · by_cases hy₂ : y ≤ (n : ℝ) + 1
    · exact Or.inl (Or.inr ⟨⟨by linarith, hy₂⟩, hy.2⟩)
    · exact Or.inr ⟨⟨by linarith, by linarith⟩, hy.2⟩

end ThreeOmittedValues
