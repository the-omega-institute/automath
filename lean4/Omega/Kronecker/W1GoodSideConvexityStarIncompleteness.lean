import Mathlib.Tactic
import Omega.Kronecker.W1SingleBoxOptimalCentering

namespace Omega.Kronecker

/-- The one-box good-side window where the star discrepancy has already frozen at `1 / q`. -/
def kroneckerGoodSideWindow (q : ℕ) (δ : ℚ) : Prop :=
  0 < δ ∧ δ < (1 : ℚ) / ((q * (q - 1) : ℕ) : ℚ)

private lemma kroneckerGoodSideQuadraticCoeff_pos (q : ℕ) (hq : 2 ≤ q) :
    0 < ((q * (q - 1) * (2 * q - 1) : ℕ) : ℚ) / 6 := by
  have hq_pos_nat : 0 < q := by omega
  have hqm1_pos_nat : 0 < q - 1 := by omega
  have h2qm1_pos_nat : 0 < 2 * q - 1 := by omega
  have hprod_pos_nat : 0 < q * (q - 1) * (2 * q - 1) := by
    exact Nat.mul_pos (Nat.mul_pos hq_pos_nat hqm1_pos_nat) h2qm1_pos_nat
  have hnum_pos : (0 : ℚ) < ((q * (q - 1) * (2 * q - 1) : ℕ) : ℚ) := by
    exact_mod_cast hprod_pos_nat
  nlinarith

private lemma kroneckerRightShiftedCriticalPoint_pos (q : ℕ) (hq : 2 ≤ q) :
    0 < kroneckerRightShiftedCriticalPoint q := by
  have h2qm1_pos_nat : 0 < 2 * q - 1 := by omega
  have hden_pos : (0 : ℚ) < (((2 * q * (2 * q - 1) : ℕ) : ℚ)) := by
    exact_mod_cast (Nat.mul_pos (by omega) h2qm1_pos_nat)
  unfold kroneckerRightShiftedCriticalPoint
  exact div_pos (by norm_num) hden_pos

private lemma kroneckerRightShiftedCriticalPoint_mem_window (q : ℕ) (hq : 2 ≤ q) :
    kroneckerGoodSideWindow q (kroneckerRightShiftedCriticalPoint q) := by
  refine ⟨kroneckerRightShiftedCriticalPoint_pos q hq, ?_⟩
  have hq_pos_nat : 0 < q := by omega
  have hqm1_pos_nat : 0 < q - 1 := by omega
  have h2qm1_pos_nat : 0 < 2 * q - 1 := by omega
  have hleft_pos : (0 : ℚ) < (((2 * q * (2 * q - 1) : ℕ) : ℚ)) := by
    exact_mod_cast (Nat.mul_pos (by omega) h2qm1_pos_nat)
  have hright_pos : (0 : ℚ) < (((q * (q - 1) : ℕ) : ℚ)) := by
    exact_mod_cast (Nat.mul_pos hq_pos_nat hqm1_pos_nat)
  have hleft_ne : (((2 * q * (2 * q - 1) : ℕ) : ℚ)) ≠ 0 := ne_of_gt hleft_pos
  have hright_ne : (((q * (q - 1) : ℕ) : ℚ)) ≠ 0 := ne_of_gt hright_pos
  have hq_one_nat : 1 ≤ q := by omega
  have h2q_one_nat : 1 ≤ 2 * q := by omega
  have hqm1_cast : (((q - 1 : ℕ) : ℚ)) = (q : ℚ) - 1 := by
    rw [Nat.cast_sub hq_one_nat]
    norm_num
  have h2qm1_cast : (((2 * q - 1 : ℕ) : ℚ)) = 2 * (q : ℚ) - 1 := by
    rw [Nat.cast_sub h2q_one_nat]
    norm_num [Nat.cast_mul]
  have hq_gt_one : (1 : ℚ) < q := by
    exact_mod_cast hq
  change 3 / (((2 * q * (2 * q - 1) : ℕ) : ℚ)) < (1 : ℚ) / ((q * (q - 1) : ℕ) : ℚ)
  field_simp [hleft_ne, hright_ne]
  norm_num [Nat.cast_mul]
  rw [hqm1_cast, h2qm1_cast]
  nlinarith

private lemma kroneckerHalfCriticalPoint_mem_window (q : ℕ) (hq : 2 ≤ q) :
    kroneckerGoodSideWindow q (kroneckerRightShiftedCriticalPoint q / 2) := by
  rcases kroneckerRightShiftedCriticalPoint_mem_window q hq with ⟨hcrit_pos, hcrit_lt⟩
  refine ⟨by nlinarith, ?_⟩
  nlinarith

/-- Paper label: `cor:xi-kronecker-good-side-convexity-star-incompleteness`.
Inside the good-side single-box chamber, the transport cost retains its strict quadratic
curvature while the star discrepancy has already frozen at the constant value `1 / q`. -/
theorem paper_xi_kronecker_good_side_convexity_star_incompleteness (q : Nat) (hq : 2 ≤ q) :
    let δStar := kroneckerRightShiftedCriticalPoint q
    let Tmin := kroneckerRightShiftedMinimum q
    (∀ δ : ℚ, kroneckerGoodSideWindow q δ →
      kroneckerGoodSideW1 q δ =
        (1 : ℚ) / (2 * q) - ((q - 1 : ℕ) : ℚ) / 2 * δ +
          ((q * (q - 1) * (2 * q - 1) : ℕ) : ℚ) / 6 * δ ^ 2 ∧
      kroneckerGoodSideStarDiscrepancy q = (1 : ℚ) / q) ∧
    0 < ((q * (q - 1) * (2 * q - 1) : ℕ) : ℚ) / 6 ∧
    kroneckerRightShiftedMinimizerSpec q ∧
    δStar = 3 / ((2 * q * (2 * q - 1) : ℕ) : ℚ) ∧
    Tmin = (((5 * q - 1 : ℕ) : ℚ) / ((8 * q * (2 * q - 1) : ℕ) : ℚ)) ∧
    Tmin < (1 : ℚ) / (2 * q) ∧
    ¬ ∃ Φ : ℚ → ℚ, ∀ δ : ℚ, kroneckerGoodSideWindow q δ →
      kroneckerGoodSideW1 q δ = Φ (kroneckerGoodSideStarDiscrepancy q) := by
  dsimp
  rcases paper_xi_kronecker_w1_single_box_optimal_centering q hq with ⟨hspec, hmin, hmin_lt⟩
  refine ⟨?_, kroneckerGoodSideQuadraticCoeff_pos q hq, hspec, rfl, hmin, hmin_lt, ?_⟩
  · intro δ hδ
    exact ⟨rfl, rfl⟩
  · intro hPhi
    rcases hPhi with ⟨Φ, hΦ⟩
    have hcrit_win : kroneckerGoodSideWindow q (kroneckerRightShiftedCriticalPoint q) :=
      kroneckerRightShiftedCriticalPoint_mem_window q hq
    have hhalf_win : kroneckerGoodSideWindow q (kroneckerRightShiftedCriticalPoint q / 2) :=
      kroneckerHalfCriticalPoint_mem_window q hq
    have hcrit_pos : 0 < kroneckerRightShiftedCriticalPoint q :=
      kroneckerRightShiftedCriticalPoint_pos q hq
    have hq_pos_nat : 0 < q := by omega
    have h2qm1_pos_nat : 0 < 2 * q - 1 := by omega
    have hden_pos_nat : 0 < 8 * q * (2 * q - 1) := by
      exact Nat.mul_pos (Nat.mul_pos (by decide) hq_pos_nat) h2qm1_pos_nat
    have hhalfden_pos_nat : 0 < 32 * q * (2 * q - 1) := by
      exact Nat.mul_pos (Nat.mul_pos (by decide) hq_pos_nat) h2qm1_pos_nat
    have hq_ne : (q : ℚ) ≠ 0 := by
      exact_mod_cast hq_pos_nat.ne'
    have hden_ne : (((8 * q * (2 * q - 1) : ℕ) : ℚ)) ≠ 0 := by
      exact_mod_cast hden_pos_nat.ne'
    have hhalfden_ne : (((32 * q * (2 * q - 1) : ℕ) : ℚ)) ≠ 0 := by
      exact_mod_cast hhalfden_pos_nat.ne'
    have hhalf :
        kroneckerGoodSideW1 q (kroneckerRightShiftedCriticalPoint q / 2) =
          (((23 * q - 7 : ℕ) : ℚ) / ((32 * q * (2 * q - 1) : ℕ) : ℚ)) := by
      have hq_one_nat : 1 ≤ q := by omega
      have h2q_one_nat : 1 ≤ 2 * q := by omega
      have h23q_seven_nat : 7 ≤ 23 * q := by omega
      have hqm1_cast : (((q - 1 : ℕ) : ℚ)) = (q : ℚ) - 1 := by
        rw [Nat.cast_sub hq_one_nat]
        norm_num
      have h2qm1_cast : (((2 * q - 1 : ℕ) : ℚ)) = 2 * (q : ℚ) - 1 := by
        rw [Nat.cast_sub h2q_one_nat]
        norm_num [Nat.cast_mul]
      have h23q7_cast : (((23 * q - 7 : ℕ) : ℚ)) = 23 * (q : ℚ) - 7 := by
        rw [Nat.cast_sub h23q_seven_nat]
        norm_num [Nat.cast_mul]
      unfold kroneckerGoodSideW1 kroneckerRightShiftedCriticalPoint
      field_simp [hq_ne, hden_ne, hhalfden_ne]
      norm_num [Nat.cast_mul]
      rw [hqm1_cast, h2qm1_cast, h23q7_cast]
      ring_nf
    have hstrict :
      kroneckerGoodSideW1 q (kroneckerRightShiftedCriticalPoint q) <
        kroneckerGoodSideW1 q (kroneckerRightShiftedCriticalPoint q / 2) := by
      have hcrit_eq :
          kroneckerGoodSideW1 q (kroneckerRightShiftedCriticalPoint q) =
            kroneckerRightShiftedMinimum q := by
        rfl
      rw [hcrit_eq, hmin, hhalf]
      have hq_one_nat : 1 ≤ q := by omega
      have h2q_one_nat : 1 ≤ 2 * q := by omega
      have h5q1_cast : (((5 * q - 1 : ℕ) : ℚ)) = 5 * (q : ℚ) - 1 := by
        have h : 1 ≤ 5 * q := by omega
        rw [Nat.cast_sub h]
        norm_num [Nat.cast_mul]
      have h23q7_cast : (((23 * q - 7 : ℕ) : ℚ)) = 23 * (q : ℚ) - 7 := by
        have h : 7 ≤ 23 * q := by omega
        rw [Nat.cast_sub h]
        norm_num [Nat.cast_mul]
      have h2qm1_cast : (((2 * q - 1 : ℕ) : ℚ)) = 2 * (q : ℚ) - 1 := by
        rw [Nat.cast_sub h2q_one_nat]
        norm_num [Nat.cast_mul]
      have hq_gt_one : (1 : ℚ) < q := by
        exact_mod_cast hq
      have hlt :
          (((5 * q - 1 : ℕ) : ℚ) / ((8 * q * (2 * q - 1) : ℕ) : ℚ)) <
            (((23 * q - 7 : ℕ) : ℚ) / ((32 * q * (2 * q - 1) : ℕ) : ℚ)) := by
        field_simp [hden_ne, hhalfden_ne]
        norm_num [Nat.cast_mul]
        rw [h5q1_cast, h23q7_cast, h2qm1_cast]
        have hq_pos : (0 : ℚ) < q := by
          exact_mod_cast hq_pos_nat
        have h2qm1_pos : (0 : ℚ) < 2 * q - 1 := by
          exact_mod_cast h2qm1_pos_nat
        have hqm1_pos : (0 : ℚ) < q - 1 := by
          nlinarith
        have hdiff : (0 : ℚ) < 24 * q * (2 * q - 1) * (q - 1) := by
          have h24_pos : (0 : ℚ) < 24 := by norm_num
          have hmul_pos : (0 : ℚ) < 24 * q * (2 * q - 1) := by
            exact mul_pos (mul_pos h24_pos hq_pos) h2qm1_pos
          exact mul_pos hmul_pos hqm1_pos
        linarith [hdiff]
      simpa using hlt
    have hsame :
        kroneckerGoodSideW1 q (kroneckerRightShiftedCriticalPoint q) =
          kroneckerGoodSideW1 q (kroneckerRightShiftedCriticalPoint q / 2) := by
      rw [hΦ _ hcrit_win, hΦ _ hhalf_win]
    exact (ne_of_lt hstrict) hsame

end Omega.Kronecker
