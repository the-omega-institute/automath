import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology

namespace Omega.Conclusion

/-- Concrete data for a fixed finite Fourier audit: a finite set of inspected frequencies and
coefficients bounded by one on those frequencies. -/
structure conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_data where
  conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies : Finset ℕ
  conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_coeff : ℕ → ℕ → ℝ
  conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_coeff_bound :
    ∀ k ∈ conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies,
      ∀ m : ℕ,
        |conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_coeff k m| ≤ 1

/-- The normalized collision gap denominator, written as the audited Fibonacci window scale. -/
def conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator
    (m : ℕ) : ℝ :=
  Nat.fib (m + 2)

theorem conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_linear_le_fib_add_two
    (m : ℕ) : m + 1 ≤ Nat.fib (m + 2) := by
  induction m with
  | zero =>
      norm_num [Nat.fib]
  | succ m ih =>
      have hfib_one : 1 ≤ Nat.fib (m + 1) := by
        have hmono := Nat.fib_mono (by omega : 1 ≤ m + 1)
        simpa [Nat.fib_one] using hmono
      have hsum : (m + 1) + 1 ≤ Nat.fib (m + 2) + Nat.fib (m + 1) :=
        Nat.add_le_add ih hfib_one
      simpa [Nat.fib_add_two, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum

/-- Energy captured by the fixed finite audit at depth `m`. -/
noncomputable def conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_capturedEnergy
    (D : conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_data) (m : ℕ) : ℝ :=
  (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies.sum fun k =>
      (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_coeff k m) ^ 2) /
    conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator m

/-- Paper-facing statement: the captured fixed-audit energy is bounded by the finite frequency
count over the normalized window denominator, hence tends to zero. -/
def conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_statement
    (D : conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_data) : Prop :=
  (∀ m : ℕ,
      0 ≤ conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_capturedEnergy D m ∧
        conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_capturedEnergy D m ≤
          (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies.card : ℝ) /
            conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator m) ∧
    Tendsto
      (fun m : ℕ =>
        conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_capturedEnergy D m)
      atTop
      (𝓝 0)

theorem conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_energy_bounds
    (D : conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_data) (m : ℕ) :
    0 ≤ conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_capturedEnergy D m ∧
      conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_capturedEnergy D m ≤
        (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies.card : ℝ) /
          conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator m := by
  classical
  have hden_nonneg :
      0 ≤ conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator m := by
    unfold conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator
    exact_mod_cast Nat.zero_le (Nat.fib (m + 2))
  have hsum_nonneg :
      0 ≤
        D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies.sum
          fun k =>
            (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_coeff k m) ^ 2 := by
    exact Finset.sum_nonneg fun k _hk => sq_nonneg _
  have hsum_le :
      (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies.sum fun k =>
          (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_coeff k m) ^ 2) ≤
        (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies.card : ℝ) := by
    calc
      (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies.sum fun k =>
          (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_coeff k m) ^ 2) ≤
          D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies.sum
            fun _k => (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro k hk
        exact (sq_le_one_iff_abs_le_one
          (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_coeff k m)).2
            (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_coeff_bound k hk m)
      _ =
          (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies.card :
            ℝ) := by
        simp
  constructor
  · unfold conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_capturedEnergy
    exact div_nonneg hsum_nonneg hden_nonneg
  · unfold conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_capturedEnergy
    exact div_le_div_of_nonneg_right hsum_le hden_nonneg

/-- Paper label: `thm:conclusion-foldbin-fixed-finite-fourier-audit-vanishing-share`. -/
theorem paper_conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share
    (D : conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_data) :
    conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_statement D := by
  constructor
  · intro m
    exact conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_energy_bounds D m
  · have hupper :
        Tendsto
          (fun m : ℕ =>
            (D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies.card :
              ℝ) /
              conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator m)
          atTop
          (𝓝 0) := by
      let C : ℝ :=
        D.conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_frequencies.card
      have hone :
          Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hmul :=
        (tendsto_const_nhds (x := C)).mul hone
      have hlinear : Tendsto (fun m : ℕ => C / ((m : ℝ) + 1)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv, mul_assoc] using hmul
      have hfib_upper :
          Tendsto
            (fun m : ℕ =>
              C /
                conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator
                  m)
            atTop
            (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlinear ?_ ?_
        · intro m
          have hC : 0 ≤ C := by dsimp [C]; positivity
          have hden_nonneg :
              0 ≤
                conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator
                  m := by
            unfold conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator
            exact_mod_cast Nat.zero_le (Nat.fib (m + 2))
          exact div_nonneg hC hden_nonneg
        · intro m
          have hC : 0 ≤ C := by dsimp [C]; positivity
          have hden_pos : 0 < ((m : ℝ) + 1) := by positivity
          have hden_ge :
              ((m : ℝ) + 1) ≤
                conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator
                  m := by
            unfold conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_fibonacciDenominator
            exact_mod_cast
              conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_linear_le_fib_add_two
                m
          exact div_le_div_of_nonneg_left hC hden_pos hden_ge
      simpa [C] using hfib_upper
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun m =>
        (conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_energy_bounds D m).1)
      (fun m =>
        (conclusion_foldbin_fixed_finite_fourier_audit_vanishing_share_energy_bounds D m).2)

end Omega.Conclusion
