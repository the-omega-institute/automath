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

/-- Paper wrapper for the even-moment gap and strict Laplace domination coming from the six
    axial weights where the visible `B₃` and `C₃` supports differ.
    thm:window6-b3c3-even-moment-gap-laplace-domination -/
theorem paper_window6_b3c3_even_moment_gap_laplace_domination :
    (axialB3Support ⊆ b3VisibleSupport ∧ axialC3Support ⊆ c3VisibleSupport) ∧
    (∀ m : Nat, 1 ≤ m → ∀ u : ℝ × ℝ × ℝ,
      axialEvenMomentGap m u =
        2 * (((2 : ℝ) ^ (2 * m)) - 1) * (u.1 ^ (2 * m) + u.2.1 ^ (2 * m) + u.2.2 ^ (2 * m))) ∧
    (∀ t : ℝ × ℝ × ℝ,
      axialLaplaceGap t =
        2 * ((Real.cosh (2 * t.1) - Real.cosh t.1) +
          (Real.cosh (2 * t.2.1) - Real.cosh t.2.1) +
          (Real.cosh (2 * t.2.2) - Real.cosh t.2.2)) ∧
      0 ≤ axialLaplaceGap t ∧
      (axialLaplaceGap t = 0 ↔ t = (0, 0, 0))) := by
  refine ⟨⟨axialB3Support_subset_visible, axialC3Support_subset_visible⟩, ?_, ?_⟩
  · intro m hm u
    let _ := hm
    unfold axialEvenMomentGap
    rw [even_gap_axis_formula, even_gap_axis_formula, even_gap_axis_formula]
    ring
  · intro t
    exact ⟨rfl, axialLaplaceGap_nonneg t, axialLaplaceGap_eq_zero_iff t⟩

end Omega.GU
