import Mathlib.Tactic
import Omega.Folding.MomentTriple

namespace Omega.OperatorAlgebra

noncomputable def foldPushforwardWeight (m : Nat) (x : Omega.X m) : ℚ :=
  (Omega.X.fiberMultiplicity x : ℚ) / (2 : ℚ) ^ m

noncomputable def foldSupervisedYaoRisk (m n : Nat) : ℚ :=
  (1 / 2 : ℚ) * ∑ x : Omega.X m,
    foldPushforwardWeight m x * (1 - foldPushforwardWeight m x) ^ n

theorem sum_foldPushforwardWeight (m : Nat) :
    ∑ x : Omega.X m, foldPushforwardWeight m x = 1 := by
  unfold foldPushforwardWeight
  have hpow : ((2 ^ m : Nat) : ℚ) = (2 : ℚ) ^ m := by
    norm_num
  have hsum : ((∑ x : Omega.X m, Omega.X.fiberMultiplicity x : Nat) : ℚ) = ((2 ^ m : Nat) : ℚ) := by
    exact_mod_cast Omega.X.fiberMultiplicity_sum_eq_pow m
  calc
    ∑ x : Omega.X m, (Omega.X.fiberMultiplicity x : ℚ) / (2 : ℚ) ^ m
        = (∑ x : Omega.X m, (Omega.X.fiberMultiplicity x : ℚ)) / (2 : ℚ) ^ m := by
            rw [Finset.sum_div]
    _ = ((∑ x : Omega.X m, Omega.X.fiberMultiplicity x : Nat) : ℚ) / (2 : ℚ) ^ m := by
          rw [← Nat.cast_sum]
    _ = ((2 ^ m : Nat) : ℚ) / (2 : ℚ) ^ m := by
          rw [hsum]
    _ = 1 := by
          rw [hpow]
          exact div_self (by positivity : (2 : ℚ) ^ m ≠ 0)

theorem foldPushforwardWeight_nonneg (m : Nat) (x : Omega.X m) :
    0 ≤ foldPushforwardWeight m x := by
  unfold foldPushforwardWeight
  positivity

theorem foldPushforwardWeight_le_one (m : Nat) (x : Omega.X m) :
    foldPushforwardWeight m x ≤ 1 := by
  have hleNat : Omega.X.fiberMultiplicity x ≤ 2 ^ m := by
    calc
      Omega.X.fiberMultiplicity x ≤ ∑ y : Omega.X m, Omega.X.fiberMultiplicity y := by
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
      _ = 2 ^ m := Omega.X.fiberMultiplicity_sum_eq_pow m
  unfold foldPushforwardWeight
  have hpow_pos : 0 < (2 : ℚ) ^ m := by positivity
  have hleRat : (Omega.X.fiberMultiplicity x : ℚ) ≤ (2 : ℚ) ^ m := by
    exact_mod_cast hleNat
  calc
    (Omega.X.fiberMultiplicity x : ℚ) / (2 : ℚ) ^ m ≤ (2 : ℚ) ^ m / (2 : ℚ) ^ m := by
      exact div_le_div_of_nonneg_right hleRat (le_of_lt hpow_pos)
    _ = 1 := by
      exact div_self (by positivity : (2 : ℚ) ^ m ≠ 0)

theorem one_sub_mul_le_pow_foldPushforwardWeight (m n : Nat) (x : Omega.X m) :
    1 - (n : ℚ) * foldPushforwardWeight m x ≤ (1 - foldPushforwardWeight m x) ^ n := by
  have hbase : -1 ≤ 1 - foldPushforwardWeight m x := by
    have hle := foldPushforwardWeight_le_one m x
    linarith
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, mul_one, one_mul] using
    (one_add_mul_sub_le_pow (a := 1 - foldPushforwardWeight m x) hbase n)

/-- Paper: `thm:op-algebra-fold-supervised-minimax-risk`.
    Under the random-label Yao prior on fold types, the exact unseen-mass risk is the weighted
    finite sum, and Bernoulli's inequality gives the universal collision lower bound. -/
theorem paper_op_algebra_fold_supervised_minimax_risk (m n : Nat) :
    foldSupervisedYaoRisk m n =
      (1 / 2 : ℚ) * ∑ x : Omega.X m,
        foldPushforwardWeight m x * (1 - foldPushforwardWeight m x) ^ n ∧
    foldSupervisedYaoRisk m n ≥
      (1 / 2 : ℚ) * (1 - (n : ℚ) * ∑ x : Omega.X m, foldPushforwardWeight m x ^ 2) := by
  constructor
  · rfl
  · unfold foldSupervisedYaoRisk
    have hsum :
        ∑ x : Omega.X m,
            foldPushforwardWeight m x * (1 - (n : ℚ) * foldPushforwardWeight m x)
          ≤ ∑ x : Omega.X m,
            foldPushforwardWeight m x * (1 - foldPushforwardWeight m x) ^ n := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (one_sub_mul_le_pow_foldPushforwardWeight m n x)
        (foldPushforwardWeight_nonneg m x)
    have hhalf :
        (1 / 2 : ℚ) *
            ∑ x : Omega.X m,
              foldPushforwardWeight m x * (1 - (n : ℚ) * foldPushforwardWeight m x)
          ≤
        (1 / 2 : ℚ) *
            ∑ x : Omega.X m,
              foldPushforwardWeight m x * (1 - foldPushforwardWeight m x) ^ n :=
      mul_le_mul_of_nonneg_left hsum (show 0 ≤ (1 / 2 : ℚ) by norm_num)
    have hrewrite :
        (1 / 2 : ℚ) *
            ∑ x : Omega.X m,
              foldPushforwardWeight m x * (1 - (n : ℚ) * foldPushforwardWeight m x)
          =
        (1 / 2 : ℚ) * (1 - (n : ℚ) * ∑ x : Omega.X m, foldPushforwardWeight m x ^ 2) := by
      calc
        (1 / 2 : ℚ) *
            ∑ x : Omega.X m,
              foldPushforwardWeight m x * (1 - (n : ℚ) * foldPushforwardWeight m x)
            =
            (1 / 2 : ℚ) *
              ∑ x : Omega.X m,
                (foldPushforwardWeight m x - (n : ℚ) * foldPushforwardWeight m x ^ 2) := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro x hx
                  ring
        _ = (1 / 2 : ℚ) *
              ((∑ x : Omega.X m, foldPushforwardWeight m x) -
                ∑ x : Omega.X m, (n : ℚ) * foldPushforwardWeight m x ^ 2) := by
              rw [Finset.sum_sub_distrib]
        _ = (1 / 2 : ℚ) *
              ((∑ x : Omega.X m, foldPushforwardWeight m x) -
                (n : ℚ) * ∑ x : Omega.X m, foldPushforwardWeight m x ^ 2) := by
              rw [Finset.mul_sum]
        _ = (1 / 2 : ℚ) * (1 - (n : ℚ) * ∑ x : Omega.X m, foldPushforwardWeight m x ^ 2) := by
              rw [sum_foldPushforwardWeight]
    calc
      (1 / 2 : ℚ) * (1 - (n : ℚ) * ∑ x : Omega.X m, foldPushforwardWeight m x ^ 2)
          =
          (1 / 2 : ℚ) *
            ∑ x : Omega.X m,
              foldPushforwardWeight m x * (1 - (n : ℚ) * foldPushforwardWeight m x) := by
                symm
                exact hrewrite
      _ ≤
          (1 / 2 : ℚ) *
            ∑ x : Omega.X m,
              foldPushforwardWeight m x * (1 - foldPushforwardWeight m x) ^ n := hhalf

end Omega.OperatorAlgebra
