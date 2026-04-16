import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic
import Omega.GU.Window6B3C3VisibleSupportThreeLeviPlanes

namespace Omega.GU

/-- The six axial weights where the `B₃` and `C₃` visible supports differ. -/
def axialB3Support : Finset Weight :=
  {(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)}

/-- The `C₃` axial support rescales the six `B₃` axial weights by `2`. -/
def axialC3Support : Finset Weight :=
  {(2, 0, 0), (-2, 0, 0), (0, 2, 0), (0, -2, 0), (0, 0, 2), (0, 0, -2)}

/-- The even-moment gap contributed by the six axial weights. -/
def axialEvenMomentGap (m : Nat) (u : ℝ × ℝ × ℝ) : ℝ :=
  ((2 * u.1) ^ (2 * m) + (-2 * u.1) ^ (2 * m) - u.1 ^ (2 * m) - (-u.1) ^ (2 * m)) +
    ((2 * u.2.1) ^ (2 * m) + (-2 * u.2.1) ^ (2 * m) - u.2.1 ^ (2 * m) - (-u.2.1) ^ (2 * m)) +
    ((2 * u.2.2) ^ (2 * m) + (-2 * u.2.2) ^ (2 * m) - u.2.2 ^ (2 * m) - (-u.2.2) ^ (2 * m))

/-- The Laplace-transform gap contributed by the six axial weights. -/
noncomputable def axialLaplaceGap (t : ℝ × ℝ × ℝ) : ℝ :=
  2 * ((Real.cosh (2 * t.1) - Real.cosh t.1) +
    (Real.cosh (2 * t.2.1) - Real.cosh t.2.1) +
    (Real.cosh (2 * t.2.2) - Real.cosh t.2.2))

lemma axialB3Support_subset_visible : axialB3Support ⊆ b3VisibleSupport := by
  intro w hw
  simp [axialB3Support, b3VisibleSupport, phiB2_12, phiB2_13, phiB2_23, zeroWeight] at hw ⊢
  aesop

lemma axialC3Support_subset_visible : axialC3Support ⊆ c3VisibleSupport := by
  intro w hw
  simp [axialC3Support, c3VisibleSupport, phiC2_12, phiC2_13, phiC2_23, zeroWeight] at hw ⊢
  aesop

lemma even_gap_axis_formula (m : Nat) (x : ℝ) :
    (2 * x) ^ (2 * m) + (-2 * x) ^ (2 * m) - x ^ (2 * m) - (-x) ^ (2 * m) =
      2 * (((2 : ℝ) ^ (2 * m)) - 1) * x ^ (2 * m) := by
  have hnegx : (-x) ^ (2 * m) = x ^ (2 * m) := by
    calc
      (-x) ^ (2 * m) = ((-x) ^ 2) ^ m := by rw [pow_mul]
      _ = (x ^ 2) ^ m := by rw [neg_sq]
      _ = x ^ (2 * m) := by rw [pow_mul]
  have hneg2x : (-2 * x) ^ (2 * m) = (2 * x) ^ (2 * m) := by
    calc
      (-2 * x) ^ (2 * m) = ((-2 * x) ^ 2) ^ m := by rw [pow_mul]
      _ = ((2 * x) ^ 2) ^ m := by congr 1; ring
      _ = (2 * x) ^ (2 * m) := by rw [pow_mul]
  rw [hnegx, hneg2x, mul_pow]
  ring_nf

lemma cosh_gap_factorization (x : ℝ) :
    Real.cosh (2 * x) - Real.cosh x = (2 * Real.cosh x + 1) * (Real.cosh x - 1) := by
  rw [Real.cosh_two_mul, Real.sinh_sq]
  ring

lemma cosh_gap_nonneg (x : ℝ) : 0 ≤ Real.cosh (2 * x) - Real.cosh x := by
  rw [cosh_gap_factorization]
  have h1 : 0 ≤ Real.cosh x - 1 := by
    linarith [Real.one_le_cosh x]
  have h2 : 0 ≤ 2 * Real.cosh x + 1 := by
    linarith [Real.one_le_cosh x]
  positivity

lemma cosh_gap_eq_zero_iff (x : ℝ) : Real.cosh (2 * x) - Real.cosh x = 0 ↔ x = 0 := by
  rw [cosh_gap_factorization]
  constructor
  · intro h
    have hpos : 0 < 2 * Real.cosh x + 1 := by
      linarith [Real.one_le_cosh x]
    have hfac : Real.cosh x - 1 = 0 := by
      exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hpos)
    have hcosh : Real.cosh x = 1 := by linarith
    have hsq : Real.sinh x ^ 2 = 0 := by
      have hsq' := Real.cosh_sq x
      rw [hcosh] at hsq'
      nlinarith
    have hsinh : Real.sinh x = 0 := by
      nlinarith [sq_nonneg (Real.sinh x), hsq]
    exact Real.sinh_eq_zero.mp hsinh
  · rintro rfl
    simp

lemma axialLaplaceGap_nonneg (t : ℝ × ℝ × ℝ) : 0 ≤ axialLaplaceGap t := by
  unfold axialLaplaceGap
  refine mul_nonneg (by positivity) ?_
  exact add_nonneg (add_nonneg (cosh_gap_nonneg t.1) (cosh_gap_nonneg t.2.1))
    (cosh_gap_nonneg t.2.2)

lemma axialLaplaceGap_eq_zero_iff (t : ℝ × ℝ × ℝ) :
    axialLaplaceGap t = 0 ↔ t = (0, 0, 0) := by
  let a := Real.cosh (2 * t.1) - Real.cosh t.1
  let b := Real.cosh (2 * t.2.1) - Real.cosh t.2.1
  let c := Real.cosh (2 * t.2.2) - Real.cosh t.2.2
  have ha0 : 0 ≤ a := cosh_gap_nonneg t.1
  have hb0 : 0 ≤ b := cosh_gap_nonneg t.2.1
  have hc0 : 0 ≤ c := cosh_gap_nonneg t.2.2
  constructor
  · intro hgap
    have hsum : a + b + c = 0 := by
      unfold axialLaplaceGap at hgap
      simp at hgap
      linarith
    have ha : a = 0 := by
      have hale : a ≤ 0 := by linarith
      exact le_antisymm hale ha0
    have hb : b = 0 := by
      have hble : b ≤ 0 := by linarith
      exact le_antisymm hble hb0
    have hc : c = 0 := by
      have hcle : c ≤ 0 := by linarith
      exact le_antisymm hcle hc0
    have ht1 : t.1 = 0 := (cosh_gap_eq_zero_iff t.1).mp (by simpa [a] using ha)
    have ht2 : t.2.1 = 0 := (cosh_gap_eq_zero_iff t.2.1).mp (by simpa [b] using hb)
    have ht3 : t.2.2 = 0 := (cosh_gap_eq_zero_iff t.2.2).mp (by simpa [c] using hc)
    ext <;> simp [ht1, ht2, ht3]
  · rintro rfl
    simp [axialLaplaceGap]

/-- The axis-only even-power contribution that distinguishes the `B₃` and `C₃`
window-6 dictionaries. -/
def axisEvenPowerSum (m : Nat) (u : ℝ × ℝ × ℝ) : ℝ :=
  u.1 ^ (2 * m) + u.2.1 ^ (2 * m) + u.2.2 ^ (2 * m)

/-- The six axis weights in the `B₃` normalization contribute `±u_i`. -/
def b3AxisEvenMoment (m : Nat) (u : ℝ × ℝ × ℝ) : ℝ :=
  2 * axisEvenPowerSum m u

/-- The six axis weights in the `C₃` normalization contribute `±2u_i`. -/
def c3AxisEvenMoment (m : Nat) (u : ℝ × ℝ × ℝ) : ℝ :=
  2 * (2 : ℝ) ^ (2 * m) * axisEvenPowerSum m u

/-- The axis-only part of the `B₃` Laplace transform. -/
noncomputable def b3AxisTheta (t : ℝ × ℝ × ℝ) : ℝ :=
  2 * (Real.cosh t.1 + Real.cosh t.2.1 + Real.cosh t.2.2)

/-- The axis-only part of the `C₃` Laplace transform. -/
noncomputable def c3AxisTheta (t : ℝ × ℝ × ℝ) : ℝ :=
  2 * (Real.cosh (2 * t.1) + Real.cosh (2 * t.2.1) + Real.cosh (2 * t.2.2))

/-- The coordinatewise cosh gap appearing in the Laplace domination formula. -/
noncomputable def axisCoshGapSum (t : ℝ × ℝ × ℝ) : ℝ :=
  (Real.cosh (2 * t.1) - Real.cosh t.1) +
    (Real.cosh (2 * t.2.1) - Real.cosh t.2.1) +
    (Real.cosh (2 * t.2.2) - Real.cosh t.2.2)

lemma axis_cosh_gap_nonneg (x : ℝ) : 0 ≤ Real.cosh (2 * x) - Real.cosh x := by
  have hcosh : 1 ≤ Real.cosh x := Real.one_le_cosh x
  have hident : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
  rw [Real.cosh_two_mul]
  nlinarith

lemma axis_cosh_gap_pos {x : ℝ} (hx : x ≠ 0) : 0 < Real.cosh (2 * x) - Real.cosh x := by
  have hcosh : 1 < Real.cosh x := (Real.one_lt_cosh).2 hx
  have hident : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
  rw [Real.cosh_two_mul]
  nlinarith

lemma axisCoshGapSum_nonneg (t : ℝ × ℝ × ℝ) : 0 ≤ axisCoshGapSum t := by
  unfold axisCoshGapSum
  nlinarith [axis_cosh_gap_nonneg t.1, axis_cosh_gap_nonneg t.2.1, axis_cosh_gap_nonneg t.2.2]

lemma axisCoshGapSum_pos_of_ne_zero {t : ℝ × ℝ × ℝ} (ht : t ≠ (0, 0, 0)) :
    0 < axisCoshGapSum t := by
  rcases t with ⟨x, y, z⟩
  change (x, y, z) ≠ (0, 0, 0) at ht
  have hxyz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 := by
    by_contra hxyz
    push_neg at hxyz
    exact ht (by ext <;> simp [hxyz.1, hxyz.2.1, hxyz.2.2])
  rcases hxyz with hx | hy | hz
  · unfold axisCoshGapSum
    nlinarith [axis_cosh_gap_pos hx, axis_cosh_gap_nonneg y, axis_cosh_gap_nonneg z]
  · unfold axisCoshGapSum
    nlinarith [axis_cosh_gap_nonneg x, axis_cosh_gap_pos hy, axis_cosh_gap_nonneg z]
  · unfold axisCoshGapSum
    nlinarith [axis_cosh_gap_nonneg x, axis_cosh_gap_nonneg y, axis_cosh_gap_pos hz]

/-- Paper wrappers for the even-moment gap and strict Laplace domination coming from the six
    axial weights where the visible `B₃` and `C₃` supports differ, together with the
    axis-only `B₃`/`C₃` comparison formulas.
    thm:window6-b3c3-even-moment-gap-laplace-domination -/
theorem paper_window6_b3c3_even_moment_gap_laplace_domination :
    (((axialB3Support ⊆ b3VisibleSupport ∧ axialC3Support ⊆ c3VisibleSupport) ∧
        (∀ m : Nat, 1 ≤ m → ∀ u : ℝ × ℝ × ℝ,
          axialEvenMomentGap m u =
            2 * (((2 : ℝ) ^ (2 * m)) - 1) *
              (u.1 ^ (2 * m) + u.2.1 ^ (2 * m) + u.2.2 ^ (2 * m))) ∧
        (∀ t : ℝ × ℝ × ℝ,
          axialLaplaceGap t =
            2 * ((Real.cosh (2 * t.1) - Real.cosh t.1) +
              (Real.cosh (2 * t.2.1) - Real.cosh t.2.1) +
              (Real.cosh (2 * t.2.2) - Real.cosh t.2.2)) ∧
          0 ≤ axialLaplaceGap t ∧
          (axialLaplaceGap t = 0 ↔ t = (0, 0, 0)))) ∧
      ((∀ m : Nat, 1 ≤ m → ∀ u : ℝ × ℝ × ℝ,
          c3AxisEvenMoment m u - b3AxisEvenMoment m u =
            2 * ((2 : ℝ) ^ (2 * m) - 1) * axisEvenPowerSum m u) ∧
        (∀ t : ℝ × ℝ × ℝ,
          c3AxisTheta t - b3AxisTheta t = 2 * axisCoshGapSum t) ∧
        (∀ t : ℝ × ℝ × ℝ, b3AxisTheta t ≤ c3AxisTheta t) ∧
        (∀ t : ℝ × ℝ × ℝ, t ≠ (0, 0, 0) → b3AxisTheta t < c3AxisTheta t))) := by
  refine ⟨?_, ?_⟩
  · refine ⟨⟨axialB3Support_subset_visible, axialC3Support_subset_visible⟩, ?_, ?_⟩
    · intro m hm u
      let _ := hm
      unfold axialEvenMomentGap
      rw [even_gap_axis_formula, even_gap_axis_formula, even_gap_axis_formula]
      ring
    · intro t
      exact ⟨rfl, axialLaplaceGap_nonneg t, axialLaplaceGap_eq_zero_iff t⟩
  · exact ⟨
      (by
        intro m _hm u
        unfold c3AxisEvenMoment b3AxisEvenMoment
        ring),
      (by
        intro t
        unfold c3AxisTheta b3AxisTheta axisCoshGapSum
        ring),
      (by
        intro t
        have hgap : c3AxisTheta t - b3AxisTheta t = 2 * axisCoshGapSum t := by
          unfold c3AxisTheta b3AxisTheta axisCoshGapSum
          ring
        have hnonneg : 0 ≤ axisCoshGapSum t := axisCoshGapSum_nonneg t
        linarith),
      (by
        intro t ht
        have hgap : c3AxisTheta t - b3AxisTheta t = 2 * axisCoshGapSum t := by
          unfold c3AxisTheta b3AxisTheta axisCoshGapSum
          ring
        have hpos : 0 < axisCoshGapSum t := axisCoshGapSum_pos_of_ne_zero ht
        linarith)⟩

end Omega.GU
