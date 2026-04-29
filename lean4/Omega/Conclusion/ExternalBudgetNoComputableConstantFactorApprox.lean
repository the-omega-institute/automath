import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The amplified two-valued budget family: the negative instance has budget `1`, while the
positive instance has budget `2^m`. -/
def conclusion_external_budget_no_computable_constant_factor_approx_budget
    (halts : Bool) (m : ℕ) : ℕ :=
  cond halts (2 ^ m) 1

/-- There is no single output value that approximates both members of the amplified two-valued
budget family within the same multiplicative factor `lam`. -/
def conclusionExternalBudgetNoComputableConstantFactorApprox : Prop :=
  ∀ lam : ℝ, 1 ≤ lam →
    ∃ m : ℕ,
      lam ^ 2 < (2 ^ m : ℝ) ∧
        ¬ ∃ a : ℕ,
          lam⁻¹ *
              (conclusion_external_budget_no_computable_constant_factor_approx_budget false m : ℝ)
              ≤ a ∧
            (a : ℝ) ≤
                lam *
                  (conclusion_external_budget_no_computable_constant_factor_approx_budget
                    false m : ℝ) ∧
            lam⁻¹ *
              (conclusion_external_budget_no_computable_constant_factor_approx_budget true m : ℝ)
              ≤ a ∧
            (a : ℝ) ≤
                lam *
                  (conclusion_external_budget_no_computable_constant_factor_approx_budget
                    true m : ℝ)

private lemma conclusion_external_budget_no_computable_constant_factor_approx_pow_growth
    (m : ℕ) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero =>
      norm_num
  | succ m ih =>
      have hpow_pos : 1 ≤ 2 ^ m := by
        exact Nat.succ_le_of_lt (pow_pos (by decide) _)
      calc
        m + 1 + 1 ≤ 2 ^ m + 1 := by
          exact Nat.succ_le_succ ih
        _ ≤ 2 ^ m + 2 ^ m := by omega
        _ = 2 ^ (m + 1) := by
          rw [Nat.pow_succ]
          omega

/-- Amplifying the `1` versus `2` budget gap by tensor powers forces the gap beyond any prescribed
constant factor, so a single output value cannot approximate both cases. This is the core
contradiction behind the no-computable-constant-factor conclusion.
    thm:conclusion-external-budget-no-computable-constant-factor-approx -/
theorem paper_conclusion_external_budget_no_computable_constant_factor_approx :
    conclusionExternalBudgetNoComputableConstantFactorApprox := by
  intro lam hlam
  let m : ℕ := Nat.ceil (lam ^ 2)
  have hm_gt : lam ^ 2 < (2 ^ m : ℝ) := by
    have hmceil : lam ^ 2 ≤ m := Nat.le_ceil (lam ^ 2)
    have hm_lt : (m : ℝ) < m + 1 := by
      exact_mod_cast Nat.lt_succ_self m
    have hlt_succ : lam ^ 2 < m + 1 := lt_of_le_of_lt hmceil hm_lt
    have hpow_nat : m + 1 ≤ 2 ^ m :=
      conclusion_external_budget_no_computable_constant_factor_approx_pow_growth m
    have hpow_real : (m + 1 : ℝ) ≤ (2 ^ m : ℝ) := by
      exact_mod_cast hpow_nat
    exact lt_of_lt_of_le hlt_succ hpow_real
  refine ⟨m, hm_gt, ?_⟩
  · intro h
    rcases h with ⟨a, hfalse_lower, hfalse_upper, htrue_lower, htrue_upper⟩
    have hlam_pos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
    have ha_le : (a : ℝ) ≤ lam := by
      simpa [conclusion_external_budget_no_computable_constant_factor_approx_budget] using
        hfalse_upper
    have hpow_le_mul : (2 ^ m : ℝ) ≤ lam * (a : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left htrue_lower (le_of_lt hlam_pos)
      have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
      simpa [conclusion_external_budget_no_computable_constant_factor_approx_budget, hlam_ne,
        mul_assoc, mul_left_comm, mul_comm] using hmul
    have hpow_le_sq : (2 ^ m : ℝ) ≤ lam ^ 2 := by
      calc
        (2 ^ m : ℝ) ≤ lam * (a : ℝ) := hpow_le_mul
        _ ≤ lam * lam := by gcongr
        _ = lam ^ 2 := by ring
    exact not_le_of_gt hm_gt hpow_le_sq

end Omega.Conclusion
