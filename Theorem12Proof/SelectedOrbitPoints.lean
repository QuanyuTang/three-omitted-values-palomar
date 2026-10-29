module

public import Theorem12Proof.TotientDivergence
public import Theorem12Proof.GammaOrbitInjectivity
public import Theorem12Proof.OrbitBounds
public import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Tactic

/-!
# Explicit modular orbit points

For each admissible index construct a determinant-one matrix in `Γ(2)`.
Its action on a fixed point of the upper half-plane gives distinct points in
one fibre of the modular lambda function. Inclusion in a particular Farey
domain is a separate question and is not asserted here.
-/

@[expose] public section

open Complex UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

namespace ThreeOmittedValues

theorem orbit_entries_exist (N : ℕ) (hN : 2 ≤ N) (i : OrbitIndexFrom N) :
    ∃ a b : ℕ, 1 ≤ a ∧ a < 4 * i.1.1 ∧
      a * i.2.1 = 2 * i.1.1 * b + 1 ∧ Odd a ∧ Odd i.2.1 ∧ Even b :=
  exists_orbit_matrix_entries (by have := i.1.2; omega) i.2.2

noncomputable def orbitA (N : ℕ) (hN : 2 ≤ N) (i : OrbitIndexFrom N) : ℕ :=
  Classical.choose (orbit_entries_exist N hN i)

noncomputable def orbitB (N : ℕ) (hN : 2 ≤ N) (i : OrbitIndexFrom N) : ℕ :=
  Classical.choose (Classical.choose_spec (orbit_entries_exist N hN i))

theorem orbit_entries_spec (N : ℕ) (hN : 2 ≤ N) (i : OrbitIndexFrom N) :
    1 ≤ orbitA N hN i ∧ orbitA N hN i < 4 * i.1.1 ∧
      orbitA N hN i * i.2.1 = 2 * i.1.1 * orbitB N hN i + 1 ∧
      Odd (orbitA N hN i) ∧ Odd i.2.1 ∧ Even (orbitB N hN i) :=
  Classical.choose_spec (Classical.choose_spec (orbit_entries_exist N hN i))

noncomputable def orbitMatrix (N : ℕ) (hN : 2 ≤ N) (i : OrbitIndexFrom N) : SL(2, ℤ) := by
  refine ⟨!![(orbitA N hN i : ℤ), (orbitB N hN i : ℤ);
             2 * (i.1.1 : ℤ), (i.2.1 : ℤ)], ?_⟩
  rw [Matrix.det_fin_two_of]
  have h : (orbitA N hN i : ℤ) * i.2.1 =
      2 * (i.1.1 : ℤ) * orbitB N hN i + 1 := by
    exact_mod_cast (orbit_entries_spec N hN i).2.2.1
  linarith

theorem orbitMatrix_lower_left (N : ℕ) (hN : 2 ≤ N) (i : OrbitIndexFrom N) :
    (orbitMatrix N hN i : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 2 * (i.1.1 : ℤ) := by
  simp [orbitMatrix]

theorem orbitMatrix_lower_right (N : ℕ) (hN : 2 ≤ N) (i : OrbitIndexFrom N) :
    (orbitMatrix N hN i : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (i.2.1 : ℤ) := by
  simp [orbitMatrix]

theorem orbitMatrix_mem_gamma_two (N : ℕ) (hN : 2 ≤ N) (i : OrbitIndexFrom N) :
    orbitMatrix N hN i ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  have hs := orbit_entries_spec N hN i
  have ha : ((orbitA N hN i : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hs.2.2.2.1
  have hd : ((i.2.1 : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hs.2.2.2.2.1
  obtain ⟨k, hk⟩ := hs.2.2.2.2.2
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have hb : ((orbitB N hN i : ℕ) : ZMod 2) = 0 := by
    rw [hk]
    push_cast
    rw [← two_mul, htwo, zero_mul]
  simp [orbitMatrix, ha, hb, hd, htwo]

noncomputable def orbitPoint (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane)
    (i : OrbitIndexFrom N) : ℂ :=
  ((orbitMatrix N hN i • τ : UpperHalfPlane) : ℂ)

theorem orbitPoint_im_pos (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane)
    (i : OrbitIndexFrom N) : 0 < (orbitPoint N hN τ i).im :=
  (orbitMatrix N hN i • τ : UpperHalfPlane).im_pos

theorem orbitPoint_lambda (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane)
    (i : OrbitIndexFrom N) :
    NoWanderingDomains.modularLambdaH (orbitPoint N hN τ i) =
      NoWanderingDomains.modularLambdaH (τ : ℂ) :=
  NoWanderingDomains.modularLambdaH_gamma2_invariant _ (orbitMatrix_mem_gamma_two N hN i) τ

theorem orbitPoint_im_formula (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane)
    (i : OrbitIndexFrom N) :
    (orbitPoint N hN τ i).im =
      (τ : ℂ).im / ((2 * (i.1.1 : ℝ) * (τ : ℂ).re + i.2.1) ^ 2 +
        (2 * (i.1.1 : ℝ) * (τ : ℂ).im) ^ 2) := by
  have hdet : (orbitA N hN i : ℝ) * (i.2.1 : ℝ) -
      (2 * (i.1.1 : ℝ)) * (orbitB N hN i : ℝ) = 1 := by
    have h : (orbitA N hN i : ℝ) * (i.2.1 : ℝ) =
        2 * (i.1.1 : ℝ) * (orbitB N hN i : ℝ) + 1 := by
      exact_mod_cast (orbit_entries_spec N hN i).2.2.1
    linarith
  have hf := mobius_imaginary_part (z := (τ : ℂ)) hdet
  change (((orbitMatrix N hN i • τ : UpperHalfPlane) : ℂ)).im = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simpa [orbitMatrix] using hf

theorem orbitPoint_height_bounds (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane)
    (i : OrbitIndexFrom N) :
    (τ : ℂ).im / (4 * ((|(τ : ℂ).re| + 1) ^ 2 + (τ : ℂ).im ^ 2) *
        (i.1.1 : ℝ) ^ 2) ≤ (orbitPoint N hN τ i).im ∧
    (orbitPoint N hN τ i).im ≤ 1 / (4 * (τ : ℂ).im * (i.1.1 : ℝ) ^ 2) := by
  have hm : (0 : ℝ) < i.1.1 := by
    have hi := i.1.2
    exact_mod_cast (show 0 < i.1.1 by omega)
  have hd : i.2.1 ≤ 2 * i.1.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp i.2.2).1).2
  have hdf : (i.2.1 : ℝ) ≤ 2 * (i.1.1 : ℝ) := by exact_mod_cast hd
  rw [orbitPoint_im_formula]
  exact selected_height_bounds hm (Nat.cast_nonneg _) hdf τ.im_pos

theorem orbitPoint_injective (N : ℕ) (hN : 2 ≤ N) (τ : UpperHalfPlane) :
    Function.Injective (orbitPoint N hN τ) := by
  intro i j hij
  have hmi : 0 < (orbitMatrix N hN i : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rw [orbitMatrix_lower_left]
    have := i.1.2
    have hm : 0 < i.1.1 := by omega
    exact_mod_cast (show 0 < 2 * i.1.1 by omega)
  have hmj : 0 < (orbitMatrix N hN j : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rw [orbitMatrix_lower_left]
    have := j.1.2
    have hm : 0 < j.1.1 := by omega
    exact_mod_cast (show 0 < 2 * j.1.1 by omega)
  have hmatrix : orbitMatrix N hN i = orbitMatrix N hN j :=
    gamma_two_orbit_injective_of_positive_lower_left _ _
      (orbitMatrix_mem_gamma_two N hN i) (orbitMatrix_mem_gamma_two N hN j)
      hmi hmj τ (UpperHalfPlane.ext hij)
  have hmval : i.1.1 = j.1.1 := by
    have h := congrArg (fun γ : SL(2, ℤ) => (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) hmatrix
    rw [orbitMatrix_lower_left, orbitMatrix_lower_left] at h
    have h' : 2 * i.1.1 = 2 * j.1.1 := by exact_mod_cast h
    omega
  have hdval : i.2.1 = j.2.1 := by
    have h := congrArg (fun γ : SL(2, ℤ) => (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) hmatrix
    rw [orbitMatrix_lower_right, orbitMatrix_lower_right] at h
    exact_mod_cast h
  cases i with
  | mk mi di =>
    cases j with
    | mk mj dj =>
      have hm : mi = mj := Subtype.ext hmval
      subst mj
      have hd : di = dj := Subtype.ext hdval
      subst dj
      rfl

end ThreeOmittedValues
