import Mathlib.Tactic
import Omega.Kronecker.W1DenominatorClosedForm

namespace Omega.Kronecker

/-- The leading quadratic coefficient on the right-shifted good-side branch. -/
def kroneckerRightShiftedQuadraticCoeff (q : ℕ) : ℚ :=
  ((q * (q - 1) * (2 * q - 1) : ℕ) : ℚ) / 6

/-- The linear coefficient magnitude on the right-shifted good-side branch. -/
def kroneckerRightShiftedLinearCoeff (q : ℕ) : ℚ :=
  ((q - 1 : ℕ) : ℚ) / 2

/-- The critical point of the good-side quadratic on the right-shifted branch. -/
def kroneckerRightShiftedCriticalPoint (q : ℕ) : ℚ :=
  3 / ((2 * q * (2 * q - 1) : ℕ) : ℚ)

/-- The minimum is the value of the quadratic at its critical point. -/
def kroneckerRightShiftedMinimum (q : ℕ) : ℚ :=
  kroneckerGoodSideW1 q (kroneckerRightShiftedCriticalPoint q)

/-- Concrete paper-facing minimizer package for the right-shifted branch. -/
def kroneckerRightShiftedMinimizerSpec (q : Nat) : Prop :=
  0 ≤ kroneckerRightShiftedCriticalPoint q ∧
    kroneckerRightShiftedCriticalPoint q ≤ 1 ∧
    ∀ δ : ℚ, kroneckerRightShiftedMinimum q ≤ kroneckerGoodSideW1 q δ

/-- The bad-side star discrepancy in the same denominator window. -/
def kroneckerBadSideStarDiscrepancy (q : ℕ) (δ : ℚ) : ℚ :=
  (1 : ℚ) / q - ((q - 1 : ℕ) : ℚ) * δ

/-- The good-side star discrepancy freezes once every denominator box contains one point. -/
def kroneckerGoodSideStarDiscrepancy (q : ℕ) : ℚ :=
  (1 : ℚ) / q

/-- The branching ratio comparing the optimal `W₁` value to the frozen good-side star discrepancy.
-/
def kroneckerRightShiftedBranchingRatio (q : ℕ) : ℚ :=
  (2 * kroneckerRightShiftedMinimum q) / kroneckerGoodSideStarDiscrepancy q

private lemma kroneckerRightShiftedQuadraticCoeff_pos (q : ℕ) (hq : 2 ≤ q) :
    0 < kroneckerRightShiftedQuadraticCoeff q := by
  have hq_pos_nat : 0 < q := by omega
  have hqm1_pos_nat : 0 < q - 1 := by omega
  have h2qm1_pos_nat : 0 < 2 * q - 1 := by omega
  have hprod_pos_nat : 0 < q * (q - 1) * (2 * q - 1) := by
    exact Nat.mul_pos (Nat.mul_pos hq_pos_nat hqm1_pos_nat) h2qm1_pos_nat
  have hnum_pos : (0 : ℚ) < ((q * (q - 1) * (2 * q - 1) : ℕ) : ℚ) := by
    exact_mod_cast hprod_pos_nat
  unfold kroneckerRightShiftedQuadraticCoeff
  nlinarith

private lemma kroneckerRightShiftedCriticalPoint_eq_vertex (q : ℕ) (hq : 2 ≤ q) :
    kroneckerRightShiftedCriticalPoint q =
      kroneckerRightShiftedLinearCoeff q / (2 * kroneckerRightShiftedQuadraticCoeff q) := by
  have hq1 : 1 ≤ q := by omega
  have hq_pos_nat : 0 < q := by omega
  have hqm1_pos_nat : 0 < q - 1 := by omega
  have h2qm1_pos_nat : 0 < 2 * q - 1 := by omega
  have hprod_pos_nat : 0 < q * (q - 1) * (2 * q - 1) := by
    exact Nat.mul_pos (Nat.mul_pos hq_pos_nat hqm1_pos_nat) h2qm1_pos_nat
  have hden_pos_nat : 0 < 2 * q * (2 * q - 1) := by
    exact Nat.mul_pos (by omega) h2qm1_pos_nat
  have hq_ne : (q : ℚ) ≠ 0 := by
    exact_mod_cast hq_pos_nat.ne'
  have hqm1_ne : (((q - 1 : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast hqm1_pos_nat.ne'
  have hden_ne : (((2 * q * (2 * q - 1) : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast hden_pos_nat.ne'
  have hprod_ne : (((q * (q - 1) * (2 * q - 1) : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast hprod_pos_nat.ne'
  unfold kroneckerRightShiftedCriticalPoint kroneckerRightShiftedLinearCoeff
    kroneckerRightShiftedQuadraticCoeff
  field_simp [hq_ne, hqm1_ne, hden_ne, hprod_ne]
  norm_num [Nat.cast_mul]
  ring_nf

private lemma kroneckerGoodSideW1_complete_square (q : ℕ) (hq : 2 ≤ q) (δ : ℚ) :
    kroneckerGoodSideW1 q δ -
        kroneckerGoodSideW1 q (kroneckerRightShiftedCriticalPoint q) =
      kroneckerRightShiftedQuadraticCoeff q * (δ - kroneckerRightShiftedCriticalPoint q) ^ 2 := by
  have hqcoeff_ne : kroneckerRightShiftedQuadraticCoeff q ≠ 0 :=
    (kroneckerRightShiftedQuadraticCoeff_pos q hq).ne'
  have hq_pos_nat : 0 < q := by omega
  have hqm1_pos_nat : 0 < q - 1 := by omega
  have h2qm1_pos_nat : 0 < 2 * q - 1 := by omega
  have hprod_pos_nat : 0 < q * (q - 1) * (2 * q - 1) := by
    exact Nat.mul_pos (Nat.mul_pos hq_pos_nat hqm1_pos_nat) h2qm1_pos_nat
  have hprod_ne : (((q * (q - 1) * (2 * q - 1) : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast hprod_pos_nat.ne'
  rw [kroneckerRightShiftedCriticalPoint_eq_vertex q hq]
  unfold kroneckerGoodSideW1 kroneckerRightShiftedLinearCoeff kroneckerRightShiftedQuadraticCoeff
  field_simp [hqcoeff_ne, hprod_ne]
  norm_num [Nat.cast_mul]
  ring_nf

theorem paper_xi_kronecker_w1_right_shifted_minimizer (q : Nat) (hq : 2 ≤ q) :
    kroneckerRightShiftedMinimizerSpec q := by
  have hcrit_nonneg : 0 ≤ kroneckerRightShiftedCriticalPoint q := by
    unfold kroneckerRightShiftedCriticalPoint
    positivity
  have hthree_le_den : (3 : ℚ) ≤ ((2 * q * (2 * q - 1) : ℕ) : ℚ) := by
    exact_mod_cast (show 3 ≤ 2 * q * (2 * q - 1) by
      have hthree_le_factor : 3 ≤ 2 * q - 1 := by omega
      have h2q_pos : 0 < 2 * q := by omega
      calc
        3 ≤ 2 * q - 1 := hthree_le_factor
        _ ≤ 2 * q * (2 * q - 1) := Nat.le_mul_of_pos_left _ h2q_pos)
  have hcrit_le_one : kroneckerRightShiftedCriticalPoint q ≤ 1 := by
    unfold kroneckerRightShiftedCriticalPoint
    have hden_ne : (((2 * q * (2 * q - 1) : ℕ) : ℚ)) ≠ 0 := by
      exact_mod_cast (show 2 * q * (2 * q - 1) ≠ 0 by
        have h2qm1_pos : 0 < 2 * q - 1 := by omega
        exact Nat.mul_pos (by omega) h2qm1_pos |>.ne')
    field_simp [hden_ne]
    exact hthree_le_den
  refine ⟨hcrit_nonneg, hcrit_le_one, ?_⟩
  intro δ
  unfold kroneckerRightShiftedMinimum
  have hcoeff_nonneg : 0 ≤ kroneckerRightShiftedQuadraticCoeff q :=
    le_of_lt (kroneckerRightShiftedQuadraticCoeff_pos q hq)
  have hsq : 0 ≤ (δ - kroneckerRightShiftedCriticalPoint q) ^ 2 := by nlinarith
  have h := kroneckerGoodSideW1_complete_square q hq δ
  nlinarith

private lemma kroneckerRightShiftedMinimum_closed_form (q : ℕ) (hq : 2 ≤ q) :
    kroneckerRightShiftedMinimum q =
      (((5 * q - 1 : ℕ) : ℚ) / ((8 * q * (2 * q - 1) : ℕ) : ℚ)) := by
  have hq_pos_nat : 0 < q := by omega
  have hq_one_nat : 1 ≤ q := by omega
  have h2qm1_pos_nat : 0 < 2 * q - 1 := by omega
  have h2q_one_nat : 1 ≤ 2 * q := by omega
  have hq_ne : (q : ℚ) ≠ 0 := by
    exact_mod_cast hq_pos_nat.ne'
  have hden_ne : (((2 * q * (2 * q - 1) : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (by omega) h2qm1_pos_nat).ne'
  have hbigden_ne : (((8 * q * (2 * q - 1) : ℕ) : ℚ)) ≠ 0 := by
    have hbigden_pos_nat : 0 < 8 * q * (2 * q - 1) := by
      exact Nat.mul_pos (Nat.mul_pos (by decide) hq_pos_nat) h2qm1_pos_nat
    exact_mod_cast hbigden_pos_nat.ne'
  have hqm1_cast : (((q - 1 : ℕ) : ℚ)) = (q : ℚ) - 1 := by
    rw [Nat.cast_sub hq_one_nat]
    norm_num
  have h2qm1_cast : (((2 * q - 1 : ℕ) : ℚ)) = 2 * (q : ℚ) - 1 := by
    rw [Nat.cast_sub h2q_one_nat]
    norm_num [Nat.cast_mul]
  have h5q1_cast : (((5 * q - 1 : ℕ) : ℚ)) = 5 * (q : ℚ) - 1 := by
    have h5q_one_nat : 1 ≤ 5 * q := by omega
    rw [Nat.cast_sub h5q_one_nat]
    norm_num [Nat.cast_mul]
  unfold kroneckerRightShiftedMinimum kroneckerGoodSideW1 kroneckerRightShiftedCriticalPoint
  field_simp [hq_ne, hden_ne, hbigden_ne]
  norm_num [Nat.cast_mul]
  rw [hqm1_cast, h2qm1_cast, h5q1_cast]
  ring

private lemma kroneckerRightShiftedBranchingRatio_closed_form (q : ℕ) (hq : 2 ≤ q) :
    kroneckerRightShiftedBranchingRatio q = (((5 * q - 1 : ℕ) : ℚ) / ((4 * (2 * q - 1) : ℕ) : ℚ)) := by
  have hq_pos_nat : 0 < q := by omega
  have h2qm1_pos_nat : 0 < 2 * q - 1 := by omega
  have hq_ne : (q : ℚ) ≠ 0 := by
    exact_mod_cast hq_pos_nat.ne'
  have h2qm1_ne : (((2 * q - 1 : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast h2qm1_pos_nat.ne'
  rw [kroneckerRightShiftedBranchingRatio, kroneckerGoodSideStarDiscrepancy,
    kroneckerRightShiftedMinimum_closed_form q hq]
  field_simp [hq_ne, h2qm1_ne]
  norm_num [Nat.cast_mul]
  ring

/-- Paper label: `cor:xi-kronecker-star-discrepancy-w1-branching`.
On the bad side, the star discrepancy is the same linear readout as `2 * W₁`; on the good side
it freezes at `1 / q` while `W₁` keeps its strict quadratic curvature. Evaluating at the
right-shifted minimizer gives the explicit branching ratio. -/
theorem paper_xi_kronecker_star_discrepancy_w1_branching (q : Nat) (hq : 2 ≤ q) :
    (∀ δ : ℚ, δ < 0 →
      kroneckerBadSideStarDiscrepancy q δ =
        (1 : ℚ) / q + ((q - 1 : ℕ) : ℚ) * (-δ) ∧
      kroneckerBadSideW1 q δ = kroneckerBadSideStarDiscrepancy q δ / 2) ∧
    (∀ δ : ℚ, 0 < δ →
      kroneckerGoodSideStarDiscrepancy q = (1 : ℚ) / q ∧
      kroneckerGoodSideW1 q δ =
        (1 : ℚ) / (2 * q) - ((q - 1 : ℕ) : ℚ) / 2 * δ +
          ((q * (q - 1) * (2 * q - 1) : ℕ) : ℚ) / 6 * δ ^ 2) ∧
    kroneckerRightShiftedMinimum q =
      (((5 * q - 1 : ℕ) : ℚ) / ((8 * q * (2 * q - 1) : ℕ) : ℚ)) ∧
    kroneckerGoodSideStarDiscrepancy q = (1 : ℚ) / q ∧
    kroneckerRightShiftedBranchingRatio q =
      (((5 * q - 1 : ℕ) : ℚ) / ((4 * (2 * q - 1) : ℕ) : ℚ)) := by
  refine ⟨?_, ?_, kroneckerRightShiftedMinimum_closed_form q hq, rfl,
    kroneckerRightShiftedBranchingRatio_closed_form q hq⟩
  · intro δ hδ
    constructor
    · unfold kroneckerBadSideStarDiscrepancy
      ring
    · unfold kroneckerBadSideW1 kroneckerBadSideStarDiscrepancy
      ring
  · intro δ hδ
    constructor
    · rfl
    · rfl

end Omega.Kronecker
