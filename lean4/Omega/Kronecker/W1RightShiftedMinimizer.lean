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

end Omega.Kronecker
