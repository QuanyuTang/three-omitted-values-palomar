module

public import Theorem12Proof.SternBrocot
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Finite semicircle chains

The height of each Farey edge is represented by a continuous square-root
function.  The finite maximum is continuous and agrees with each individual
edge on that edge's horizontal interval.  Pasting the finite chains across
the integers is a separate task.
-/

@[expose] public section

namespace ThreeOmittedValues

noncomputable section

/-- The upper semicircle over an edge, extended by zero outside its interval. -/
def edgeHeight (e : RationalEdge) (x : ℝ) : ℝ :=
  Real.sqrt ((x - endpointCoordinate e.left) * (endpointCoordinate e.right - x))

theorem edgeHeight_nonneg (e : RationalEdge) (x : ℝ) : 0 ≤ edgeHeight e x :=
  Real.sqrt_nonneg _

theorem continuous_edgeHeight (e : RationalEdge) : Continuous (edgeHeight e) := by
  unfold edgeHeight
  fun_prop

/-- A semicircle is bounded by half of its horizontal width. -/
theorem edgeHeight_le_half_width (e : RationalEdge)
    (he : endpointCoordinate e.left ≤ endpointCoordinate e.right) (x : ℝ) :
    edgeHeight e x ≤ edgeWidth e / 2 := by
  have hwidth : 0 ≤ edgeWidth e / 2 := by dsimp [edgeWidth]; linarith
  have hsquare : (x - endpointCoordinate e.left) * (endpointCoordinate e.right - x) ≤
      (edgeWidth e / 2) ^ 2 := by
    dsimp [edgeWidth]
    nlinarith [sq_nonneg (x - (endpointCoordinate e.left + endpointCoordinate e.right) / 2)]
  calc
    edgeHeight e x ≤ Real.sqrt ((edgeWidth e / 2) ^ 2) := Real.sqrt_le_sqrt hsquare
    _ = edgeWidth e / 2 := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hwidth]

theorem edgeHeight_eq_zero_of_le_left (e : RationalEdge)
    (he : endpointCoordinate e.left ≤ endpointCoordinate e.right)
    {x : ℝ} (hx : x ≤ endpointCoordinate e.left) : edgeHeight e x = 0 := by
  apply Real.sqrt_eq_zero_of_nonpos
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem edgeHeight_eq_zero_of_right_le (e : RationalEdge)
    (he : endpointCoordinate e.left ≤ endpointCoordinate e.right)
    {x : ℝ} (hx : endpointCoordinate e.right ≤ x) : edgeHeight e x = 0 := by
  apply Real.sqrt_eq_zero_of_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

/-- Inside its edge interval, the height satisfies the semicircle equation. -/
theorem edgeHeight_sq_of_inside (e : RationalEdge) {x : ℝ}
    (hleft : endpointCoordinate e.left ≤ x) (hright : x ≤ endpointCoordinate e.right) :
    edgeHeight e x ^ 2 =
      (x - endpointCoordinate e.left) * (endpointCoordinate e.right - x) := by
  exact Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr hright))

/-- All semicircles of a depth-`n` finite chain lie below `1/(2(n+1))`. -/
theorem sternBrocotEdges_height_function_bound (n : ℕ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges n) (x : ℝ) :
    edgeHeight e x ≤ 1 / (2 * ((n + 1 : ℕ) : ℝ)) := by
  have hgap := sternBrocotEdges_gap n he
  have hhalf : edgeWidth e / 2 =
      1 / (2 * (e.left.denominator : ℝ) * e.right.denominator) := by
    dsimp [edgeWidth, endpointCoordinate]
    rw [hgap]
    ring
  exact (edgeHeight_le_half_width e (sternBrocotEdges_strict n he).le x).trans
    (by simpa [hhalf] using sternBrocotEdges_height_bound n he)

/-- The finite maximum of the heights of all edges in a chain. -/
def chainHeight (es : List RationalEdge) (x : ℝ) : ℝ :=
  es.foldr (fun e acc => max (edgeHeight e x) acc) 0

theorem chainHeight_nonneg (es : List RationalEdge) (x : ℝ) : 0 ≤ chainHeight es x := by
  induction es with
  | nil => exact le_rfl
  | cons e es ih =>
      change 0 ≤ max (edgeHeight e x) (chainHeight es x)
      exact ih.trans (le_max_right _ _)

theorem continuous_chainHeight (es : List RationalEdge) : Continuous (chainHeight es) := by
  induction es with
  | nil => exact continuous_const
  | cons e es ih =>
      change Continuous (fun x => max (edgeHeight e x) (chainHeight es x))
      exact (continuous_edgeHeight e).max ih

theorem chainHeight_le_of_forall (es : List RationalEdge) (x C : ℝ) (hC : 0 ≤ C)
    (h : ∀ e ∈ es, edgeHeight e x ≤ C) : chainHeight es x ≤ C := by
  induction es with
  | nil => exact hC
  | cons e es ih =>
      change max (edgeHeight e x) (chainHeight es x) ≤ C
      exact max_le (h e (by simp)) (ih (fun f hf => h f (by simp [hf])))

theorem edgeHeight_le_chainHeight {es : List RationalEdge} {e : RationalEdge}
    (he : e ∈ es) (x : ℝ) : edgeHeight e x ≤ chainHeight es x := by
  induction es with
  | nil => simp at he
  | cons f es ih =>
      change edgeHeight e x ≤ max (edgeHeight f x) (chainHeight es x)
      rcases List.mem_cons.mp he with rfl | he
      · exact le_max_left _ _
      · exact (ih he).trans (le_max_right _ _)

/-- A finite chain's height inherits the uniform semicircle bound. -/
theorem sternBrocot_chainHeight_bound (n : ℕ) (x : ℝ) :
    chainHeight (sternBrocotEdges n) x ≤ 1 / (2 * ((n + 1 : ℕ) : ℝ)) := by
  apply chainHeight_le_of_forall _ _ _ (by positivity)
  intro e he
  exact sternBrocotEdges_height_function_bound n he x

/-- The interiors of two different edges do not overlap. -/
def EdgesNonoverlapping (e f : RationalEdge) : Prop :=
  endpointCoordinate e.right ≤ endpointCoordinate f.left ∨
    endpointCoordinate f.right ≤ endpointCoordinate e.left

instance : Std.Symm EdgesNonoverlapping :=
  ⟨fun _ _ h => h.elim Or.inr Or.inl⟩

theorem sternBrocotEdges_nonoverlap (n : ℕ) {e f : RationalEdge}
    (he : e ∈ sternBrocotEdges n) (hf : f ∈ sternBrocotEdges n) (hne : e ≠ f) :
    EdgesNonoverlapping e f := by
  have hpair : (sternBrocotEdges n).Pairwise EdgesNonoverlapping :=
    (sternBrocotEdges_pairwise_ordered n).imp (fun h => Or.inl h.1)
  exact hpair.forall he hf hne

/-- On an edge interval the maximum is exactly that edge's semicircle. -/
theorem sternBrocot_chainHeight_eq_edge (n : ℕ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges n) {x : ℝ}
    (hxleft : endpointCoordinate e.left ≤ x) (hxright : x ≤ endpointCoordinate e.right) :
    chainHeight (sternBrocotEdges n) x = edgeHeight e x := by
  apply le_antisymm
  · apply chainHeight_le_of_forall _ _ _ (edgeHeight_nonneg e x)
    intro f hf
    by_cases hfe : f = e
    · subst f
      exact le_rfl
    · have hdis := sternBrocotEdges_nonoverlap n he hf (Ne.symm hfe)
      have hfinc := (sternBrocotEdges_strict n hf).le
      rcases hdis with hforward | hbackward
      · rw [edgeHeight_eq_zero_of_le_left f hfinc (hxright.trans hforward)]
        exact edgeHeight_nonneg e x
      · rw [edgeHeight_eq_zero_of_right_le f hfinc (hbackward.trans hxleft)]
        exact edgeHeight_nonneg e x
  · exact edgeHeight_le_chainHeight he x

/-- Each finite height function vanishes outside the unit interval, including
both endpoints; this is the matching condition for pasting adjacent chains. -/
theorem sternBrocot_chainHeight_eq_zero_outside (n : ℕ) {x : ℝ}
    (hx : x ≤ 0 ∨ 1 ≤ x) : chainHeight (sternBrocotEdges n) x = 0 := by
  apply le_antisymm
  · apply chainHeight_le_of_forall _ _ _ le_rfl
    intro e he
    have hcoords := sternBrocotEdges_coordinates_in_unit n he
    have hinc := (sternBrocotEdges_strict n he).le
    rcases hx with hleft | hright
    · rw [edgeHeight_eq_zero_of_le_left e hinc (hleft.trans hcoords.1.1)]
    · rw [edgeHeight_eq_zero_of_right_le e hinc (hcoords.2.2.trans hright)]
  · exact chainHeight_nonneg _ _

/-- The union of the upper semicircular arcs in a finite chain. -/
def finiteChainArcs (n : ℕ) : Set ℂ :=
  {z | ∃ e ∈ sternBrocotEdges n, endpointCoordinate e.left ≤ z.re ∧
    z.re ≤ endpointCoordinate e.right ∧ z.im = edgeHeight e z.re}

/-- The graph of the finite height function over `[0,1]`. -/
def finiteChainGraph (n : ℕ) : Set ℂ :=
  {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ z.im = chainHeight (sternBrocotEdges n) z.re}

/-- The finite union of Farey semicircles is exactly this continuous graph. -/
theorem finiteChainArcs_eq_graph (n : ℕ) : finiteChainArcs n = finiteChainGraph n := by
  ext z
  constructor
  · rintro ⟨e, he, hleft, hright, hz⟩
    have hcoords := sternBrocotEdges_coordinates_in_unit n he
    refine ⟨hcoords.1.1.trans hleft, hright.trans hcoords.2.2, ?_⟩
    rw [sternBrocot_chainHeight_eq_edge n he hleft hright]
    exact hz
  · rintro ⟨h0, h1, hz⟩
    obtain ⟨e, he, hleft, hright⟩ := sternBrocotEdges_cover n h0 h1
    refine ⟨e, he, hleft, hright, ?_⟩
    rw [← sternBrocot_chainHeight_eq_edge n he hleft hright]
    exact hz

end

end ThreeOmittedValues
