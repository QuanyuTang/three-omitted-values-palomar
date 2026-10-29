module

public import Theorem12Proof.FareyElementary
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Chain
import Mathlib.Tactic

/-!
# Finite Stern–Brocot refinements

These finite refinements establish the Farey-sequence facts used later to
construct the locally finite infinite path and its boundary parametrization.
-/

@[expose] public section

namespace ThreeOmittedValues

/-- A rational endpoint represented by a natural numerator and denominator. -/
structure RationalEndpoint where
  numerator : ℕ
  denominator : ℕ
  deriving DecidableEq

/-- A directed edge in the nonnegative Stern–Brocot interval. -/
structure RationalEdge where
  left : RationalEndpoint
  right : RationalEndpoint
  deriving DecidableEq

def mediant (u v : RationalEndpoint) : RationalEndpoint :=
  ⟨u.numerator + v.numerator, u.denominator + v.denominator⟩

def lowerHalf (e : RationalEdge) : RationalEdge := ⟨e.left, mediant e.left e.right⟩
def upperHalf (e : RationalEdge) : RationalEdge := ⟨mediant e.left e.right, e.right⟩

def initialEdge : RationalEdge := ⟨⟨0, 1⟩, ⟨1, 1⟩⟩

/-- Uniformly insert a mediant in each edge at every refinement. -/
def sternBrocotEdges : ℕ → List RationalEdge
  | 0 => [initialEdge]
  | n + 1 => (sternBrocotEdges n).flatMap fun e => [lowerHalf e, upperHalf e]

/-- Adjacent edges are joined at the same rational endpoint. -/
def EdgesJoin (e f : RationalEdge) : Prop := e.right = f.left

theorem refine_edges_chain (es : List RationalEdge) (h : es.IsChain EdgesJoin) :
    (es.flatMap fun e => [lowerHalf e, upperHalf e]).IsChain EdgesJoin := by
  induction es with
  | nil => exact List.IsChain.nil
  | cons a es ih =>
      cases es with
      | nil =>
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          exact List.IsChain.cons_cons rfl (List.IsChain.singleton _)
      | cons b rest =>
          have hab : EdgesJoin a b := (List.isChain_cons_cons.mp h).1
          have htail : (b :: rest).IsChain EdgesJoin := (List.isChain_cons_cons.mp h).2
          have hrefined := ih htail
          simp only [List.flatMap_cons, List.cons_append, List.nil_append]
          apply List.IsChain.cons_cons (show EdgesJoin (lowerHalf a) (upperHalf a) from rfl)
          apply List.IsChain.cons_cons (show EdgesJoin (upperHalf a) (lowerHalf b) from hab)
          exact hrefined

/-- Each finite refinement is a connected chain of edges. -/
theorem sternBrocotEdges_chain (n : ℕ) : (sternBrocotEdges n).IsChain EdgesJoin := by
  induction n with
  | zero => exact List.IsChain.singleton _
  | succ n ih => exact refine_edges_chain _ ih

def leftmostEndpoint (es : List RationalEdge) : Option RationalEndpoint :=
  es.head?.map RationalEdge.left

def rightmostEndpoint (es : List RationalEdge) : Option RationalEndpoint :=
  es.getLast?.map RationalEdge.right

theorem refine_edges_leftmost (es : List RationalEdge) :
    leftmostEndpoint (es.flatMap fun e => [lowerHalf e, upperHalf e]) = leftmostEndpoint es := by
  cases es with
  | nil => rfl
  | cons e es => simp [leftmostEndpoint, lowerHalf]

theorem refine_edges_rightmost (es : List RationalEdge) :
    rightmostEndpoint (es.flatMap fun e => [lowerHalf e, upperHalf e]) = rightmostEndpoint es := by
  induction es with
  | nil => rfl
  | cons a es ih =>
      cases es with
      | nil => simp [rightmostEndpoint, upperHalf]
      | cons b rest =>
          have hnonempty : ((b :: rest).flatMap fun e => [lowerHalf e, upperHalf e]) ≠ [] := by
            simp
          change ([lowerHalf a, upperHalf a] ++
            ((b :: rest).flatMap fun e => [lowerHalf e, upperHalf e])).getLast?.map
              RationalEdge.right = (a :: b :: rest).getLast?.map RationalEdge.right
          rw [List.getLast?_append_of_ne_nil _ hnonempty, List.getLast?_cons_cons]
          exact ih

/-- All refinements begin at `0/1` and end at `1/1`. -/
theorem sternBrocotEdges_endpoints (n : ℕ) :
    leftmostEndpoint (sternBrocotEdges n) = some ⟨0, 1⟩ ∧
      rightmostEndpoint (sternBrocotEdges n) = some ⟨1, 1⟩ := by
  induction n with
  | zero => constructor <;> rfl
  | succ n ih =>
      change leftmostEndpoint ((sternBrocotEdges n).flatMap
          (fun e => [lowerHalf e, upperHalf e])) = some ⟨0, 1⟩ ∧
        rightmostEndpoint ((sternBrocotEdges n).flatMap
          (fun e => [lowerHalf e, upperHalf e])) = some ⟨1, 1⟩
      rw [refine_edges_leftmost, refine_edges_rightmost]
      exact ih

def HasEndpoint (es : List RationalEdge) (v : RationalEndpoint) : Prop :=
  ∃ e ∈ es, e.left = v ∨ e.right = v

theorem refine_edges_preserves_endpoint {es : List RationalEdge} {v : RationalEndpoint}
    (h : HasEndpoint es v) :
    HasEndpoint (es.flatMap fun e => [lowerHalf e, upperHalf e]) v := by
  obtain ⟨e, he, hl | hr⟩ := h
  · refine ⟨lowerHalf e, List.mem_flatMap.mpr ⟨e, he, ?_⟩, Or.inl hl⟩
    simp
  · refine ⟨upperHalf e, List.mem_flatMap.mpr ⟨e, he, ?_⟩, Or.inr hr⟩
    simp

/-- The midpoint `1/2` remains a vertex at every positive depth. -/
theorem sternBrocotEdges_has_half (n : ℕ) :
    HasEndpoint (sternBrocotEdges (n + 1)) ⟨1, 2⟩ := by
  induction n with
  | zero =>
      refine ⟨lowerHalf initialEdge, ?_, Or.inr rfl⟩
      simp [sternBrocotEdges]
  | succ n ih =>
      exact refine_edges_preserves_endpoint ih

def IsGoodEdge (n : ℕ) (e : RationalEdge) : Prop :=
  1 ≤ e.left.denominator ∧ 1 ≤ e.right.denominator ∧
  e.left.denominator * e.right.numerator =
    e.left.numerator * e.right.denominator + 1 ∧
  n + 2 ≤ e.left.denominator + e.right.denominator

def IsUnitEdge (e : RationalEdge) : Prop :=
  e.left.numerator ≤ e.left.denominator ∧ e.right.numerator ≤ e.right.denominator

theorem sternBrocotEdges_unit (n : ℕ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges n) : IsUnitEdge e := by
  induction n generalizing e with
  | zero =>
      simp only [sternBrocotEdges, List.mem_singleton] at he
      subst e
      simp [IsUnitEdge, initialEdge]
  | succ n ih =>
      simp only [sternBrocotEdges, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
      obtain ⟨parent, hparent, hsplit⟩ := he
      obtain ⟨hl, hr⟩ := ih hparent
      rcases hsplit with hleft | hright
      · subst e
        dsimp [IsUnitEdge, lowerHalf, mediant]
        exact ⟨hl, Nat.add_le_add hl hr⟩
      · subst e
        dsimp [IsUnitEdge, upperHalf, mediant]
        exact ⟨Nat.add_le_add hl hr, hr⟩

/-- Mediant subdivision preserves Farey adjacency and increases the minimum
sum of neighboring denominators. -/
theorem lowerHalf_good {n : ℕ} {e : RationalEdge} (h : IsGoodEdge n e) :
    IsGoodEdge (n + 1) (lowerHalf e) := by
  rcases h with ⟨hl, hr, hdet, hsum⟩
  dsimp [IsGoodEdge, lowerHalf, mediant]
  refine ⟨hl, by omega, ?_, by omega⟩
  nlinarith [hdet]

theorem upperHalf_good {n : ℕ} {e : RationalEdge} (h : IsGoodEdge n e) :
    IsGoodEdge (n + 1) (upperHalf e) := by
  rcases h with ⟨hl, hr, hdet, hsum⟩
  dsimp [IsGoodEdge, upperHalf, mediant]
  refine ⟨by omega, hr, ?_, by omega⟩
  nlinarith [hdet]

/-- Every finite Stern–Brocot edge is an adjacent pair, and its denominator
sum is at least the refinement depth plus two. -/
theorem sternBrocotEdges_good (n : ℕ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges n) : IsGoodEdge n e := by
  induction n generalizing e with
  | zero =>
      simp only [sternBrocotEdges, List.mem_singleton] at he
      subst e
      simp [IsGoodEdge, initialEdge]
  | succ n ih =>
      simp only [sternBrocotEdges, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
      obtain ⟨parent, hparent, hsplit⟩ := he
      rcases hsplit with hleft | hright
      · subst e
        exact lowerHalf_good (ih hparent)
      · subst e
        exact upperHalf_good (ih hparent)

/-- The product of the endpoint denominators is at least `n+1`. -/
theorem sternBrocotEdges_denominator_product (n : ℕ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges n) :
    n + 1 ≤ e.left.denominator * e.right.denominator := by
  obtain ⟨hl, hr, _hdet, hsum⟩ := sternBrocotEdges_good n he
  exact farey_denominator_product_bound hl hr (by omega)

/-- A determinant-one edge has reduced fractions at both ends. -/
theorem goodEdge_coprime {n : ℕ} {e : RationalEdge} (he : IsGoodEdge n e) :
    e.left.numerator.Coprime e.left.denominator ∧
      e.right.numerator.Coprime e.right.denominator := by
  obtain ⟨_hl, _hr, hdet, _hsum⟩ := he
  constructor
  · change Nat.gcd e.left.numerator e.left.denominator = 1
    apply Nat.dvd_one.mp
    have h1 : Nat.gcd e.left.numerator e.left.denominator ∣
        e.left.denominator * e.right.numerator :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
    have h2 : Nat.gcd e.left.numerator e.left.denominator ∣
        e.left.numerator * e.right.denominator :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
    rw [hdet] at h1
    have h3 := Nat.dvd_sub h1 h2
    simpa using h3
  · change Nat.gcd e.right.numerator e.right.denominator = 1
    apply Nat.dvd_one.mp
    have h1 : Nat.gcd e.right.numerator e.right.denominator ∣
        e.left.denominator * e.right.numerator :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
    have h2 : Nat.gcd e.right.numerator e.right.denominator ∣
        e.left.numerator * e.right.denominator :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
    rw [hdet] at h1
    have h3 := Nat.dvd_sub h1 h2
    simpa using h3

/-- Adjacent endpoints are strictly ordered and their real-coordinate gap
is the reciprocal of the denominator product. -/
theorem sternBrocotEdges_gap (n : ℕ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges n) :
    (e.right.numerator : ℝ) / e.right.denominator -
        (e.left.numerator : ℝ) / e.left.denominator =
      1 / ((e.left.denominator : ℝ) * e.right.denominator) := by
  obtain ⟨hl, hr, hdet, _hsum⟩ := sternBrocotEdges_good n he
  have hl' : (0 : ℝ) < e.left.denominator := by exact_mod_cast (by omega : 0 < e.left.denominator)
  have hr' : (0 : ℝ) < e.right.denominator := by exact_mod_cast (by omega : 0 < e.right.denominator)
  have hdet' : (e.left.denominator : ℝ) * e.right.numerator -
      (e.left.numerator : ℝ) * e.right.denominator = 1 := by
    have h : (e.left.denominator : ℝ) * e.right.numerator =
        (e.left.numerator : ℝ) * e.right.denominator + 1 := by exact_mod_cast hdet
    linarith
  exact farey_neighbor_gap hl' hr' hdet'

noncomputable def endpointCoordinate (u : RationalEndpoint) : ℝ :=
  (u.numerator : ℝ) / u.denominator

/-- Every endpoint of a finite chain lies in `[0,1]`. -/
theorem sternBrocotEdges_coordinates_in_unit (n : ℕ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges n) :
    endpointCoordinate e.left ∈ Set.Icc 0 1 ∧ endpointCoordinate e.right ∈ Set.Icc 0 1 := by
  obtain ⟨hl, hr, _, _⟩ := sternBrocotEdges_good n he
  obtain ⟨hul, hur⟩ := sternBrocotEdges_unit n he
  have hl' : (0 : ℝ) < e.left.denominator := by exact_mod_cast (by omega : 0 < e.left.denominator)
  have hr' : (0 : ℝ) < e.right.denominator := by exact_mod_cast (by omega : 0 < e.right.denominator)
  constructor
  · constructor
    · exact div_nonneg (Nat.cast_nonneg _) hl'.le
    · apply (div_le_one hl').2
      exact_mod_cast hul
  · constructor
    · exact div_nonneg (Nat.cast_nonneg _) hr'.le
    · apply (div_le_one hr').2
      exact_mod_cast hur

/-- Every edge in a finite refinement points strictly from left to right. -/
theorem sternBrocotEdges_strict (n : ℕ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges n) : endpointCoordinate e.left < endpointCoordinate e.right := by
  have hgap := sternBrocotEdges_gap n he
  obtain ⟨hl, hr, _, _⟩ := sternBrocotEdges_good n he
  have hl' : (0 : ℝ) < e.left.denominator := by exact_mod_cast (by omega : 0 < e.left.denominator)
  have hr' : (0 : ℝ) < e.right.denominator := by exact_mod_cast (by omega : 0 < e.right.denominator)
  have hp : 0 < (1 : ℝ) / ((e.left.denominator : ℝ) * e.right.denominator) := by positivity
  dsimp [endpointCoordinate]
  linarith

/-- `e` precedes `f`, and `f` has strictly increasing endpoints. -/
def EdgeBefore (e f : RationalEdge) : Prop :=
  endpointCoordinate e.right ≤ endpointCoordinate f.left ∧
    endpointCoordinate f.left < endpointCoordinate f.right

/-- Later edges have disjoint interiors from earlier edges. -/
theorem sternBrocotEdges_pairwise_ordered (n : ℕ) :
    (sternBrocotEdges n).Pairwise EdgeBefore := by
  letI : IsTrans RationalEdge EdgeBefore := ⟨fun _ _ _ hab hbc =>
    ⟨hab.1.trans (hab.2.le.trans hbc.1), hbc.2⟩⟩
  have hchain : (sternBrocotEdges n).IsChain EdgeBefore := by
    apply (sternBrocotEdges_chain n).imp_of_mem_imp
    intro e f _he hf hjoin
    refine ⟨?_, sternBrocotEdges_strict n hf⟩
    dsimp [EdgesJoin] at hjoin
    rw [hjoin]
  exact List.isChain_iff_pairwise.mp hchain

/-- No finite refinement repeats an edge. -/
theorem sternBrocotEdges_nodup (n : ℕ) : (sternBrocotEdges n).Nodup := by
  apply (sternBrocotEdges_pairwise_ordered n).imp
  intro e f hef heq
  subst f
  exact (not_lt_of_ge hef.1) hef.2

/-- Every point of `[0, 1]` is covered by one of the refined edge intervals. -/
theorem sternBrocotEdges_cover (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ e ∈ sternBrocotEdges n, endpointCoordinate e.left ≤ x ∧
      x ≤ endpointCoordinate e.right := by
  induction n with
  | zero =>
      refine ⟨initialEdge, by simp [sternBrocotEdges], ?_, ?_⟩
      · simpa [endpointCoordinate, initialEdge] using hx0
      · simpa [endpointCoordinate, initialEdge] using hx1
  | succ n ih =>
      obtain ⟨e, he, hleft, hright⟩ := ih
      have hlow : lowerHalf e ∈ sternBrocotEdges (n + 1) := by
        simp only [sternBrocotEdges, List.mem_flatMap]
        exact ⟨e, he, by simp⟩
      have hhigh : upperHalf e ∈ sternBrocotEdges (n + 1) := by
        simp only [sternBrocotEdges, List.mem_flatMap]
        exact ⟨e, he, by simp⟩
      by_cases hmid : x ≤ endpointCoordinate (mediant e.left e.right)
      · exact ⟨lowerHalf e, hlow, hleft, hmid⟩
      · exact ⟨upperHalf e, hhigh, le_of_not_ge hmid, hright⟩

noncomputable def edgeWidth (e : RationalEdge) : ℝ :=
  endpointCoordinate e.right - endpointCoordinate e.left

theorem refine_edges_sum_width (es : List RationalEdge) :
    ((es.flatMap fun e => [lowerHalf e, upperHalf e]).map edgeWidth).sum =
      (es.map edgeWidth).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, ih]
      dsimp [edgeWidth, lowerHalf, upperHalf]
      ring

/-- The sum of horizontal widths in every refinement is one. -/
theorem sternBrocotEdges_sum_width (n : ℕ) :
    ((sternBrocotEdges n).map edgeWidth).sum = 1 := by
  induction n with
  | zero => norm_num [sternBrocotEdges, edgeWidth, endpointCoordinate, initialEdge]
  | succ n ih =>
      change (((sternBrocotEdges n).flatMap fun e => [lowerHalf e, upperHalf e]).map edgeWidth).sum = 1
      rw [refine_edges_sum_width]
      exact ih

/-- The Euclidean height of each semicircular edge is at most
`1 / (2 (n+1))`. -/
theorem sternBrocotEdges_height_bound (n : ℕ) {e : RationalEdge}
    (he : e ∈ sternBrocotEdges n) :
    (1 : ℝ) / (2 * e.left.denominator * e.right.denominator) ≤
      1 / (2 * ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨hl, hr, _hdet, _hsum⟩ := sternBrocotEdges_good n he
  have hl' : (0 : ℝ) < e.left.denominator := by exact_mod_cast (by omega : 0 < e.left.denominator)
  have hr' : (0 : ℝ) < e.right.denominator := by exact_mod_cast (by omega : 0 < e.right.denominator)
  have hn' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_lt_succ n)
  have hp : ((n + 1 : ℕ) : ℝ) ≤ (e.left.denominator : ℝ) * e.right.denominator := by
    exact_mod_cast sternBrocotEdges_denominator_product n he
  exact farey_semicircle_height_le hn' hl' hr' hp

end ThreeOmittedValues
