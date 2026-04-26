import Omega.Zeta.HankelFinitefieldRandomCompletionNondegenerate
import Mathlib.Tactic

namespace Omega.Zeta

/-- Lower bound on the one-shot success probability for the finite-field Hankel completion:
at most one sample out of `p` can be singular. -/
noncomputable def
    xi_hankel_finitefield_random_completion_las_vegas_expected_success_probability_lb
    {p : ℕ} [Fact p.Prime] : ℚ :=
  1 - 1 / (p : ℚ)

/-- Geometric-trial upper bound for the expected number of Las Vegas resamplings. -/
noncomputable def
    xi_hankel_finitefield_random_completion_las_vegas_expected_trials_bound
    {p : ℕ} [Fact p.Prime] : ℚ :=
  1 /
    xi_hankel_finitefield_random_completion_las_vegas_expected_success_probability_lb (p := p)

/-- Paper-facing Las Vegas completion package: the one-step nondegenerate completion theorem gives
the unique-extension certificate, the determinant failure probability is at most `1 / p`, the
resulting geometric expected trial count is `p / (p - 1)`, and this is at most `2` for primes. -/
def xi_hankel_finitefield_random_completion_las_vegas_expected_statement
    {p : ℕ} [Fact p.Prime] (a0 a1 : ZMod p) (_ha0 : a0 != 0) : Prop :=
  hankelSeedFailureProbabilityBound a0 a1 ∧
    hankelSeedUniqueExtensionOnNonvanishingLocus a0 a1 ∧
    xi_hankel_finitefield_random_completion_las_vegas_expected_success_probability_lb (p := p) =
      ((p : ℚ) - 1) / p ∧
    xi_hankel_finitefield_random_completion_las_vegas_expected_trials_bound (p := p) =
      (p : ℚ) / ((p : ℚ) - 1) ∧
    xi_hankel_finitefield_random_completion_las_vegas_expected_trials_bound (p := p) ≤ 2

/-- Paper label: `cor:xi-hankel-finitefield-random-completion-las-vegas-expected`. The
determinant-vanishing set has size at most one by the nondegenerate completion theorem, so a
uniform trial succeeds with probability at least `(p - 1) / p`; independent resampling is then a
geometric process with expected trial count at most `p / (p - 1) ≤ 2`. -/
theorem paper_xi_hankel_finitefield_random_completion_las_vegas_expected
    {p : Nat} [Fact p.Prime] (a0 a1 : ZMod p) (ha0 : a0 != 0) :
    xi_hankel_finitefield_random_completion_las_vegas_expected_statement a0 a1 ha0 := by
  have hp : Nat.Prime p := Fact.out
  have ha0' : a0 ≠ 0 := by
    simpa using ha0
  have hbase :=
    paper_xi_hankel_finitefield_random_completion_nondegenerate a0 a1 ha0'
  have hp0q : (p : ℚ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hp1q : 0 < (p : ℚ) - 1 := by
    have hp1 : (1 : ℚ) < p := by
      exact_mod_cast hp.one_lt
    linarith
  have hsuccess :
      xi_hankel_finitefield_random_completion_las_vegas_expected_success_probability_lb (p := p) =
        ((p : ℚ) - 1) / p := by
    unfold xi_hankel_finitefield_random_completion_las_vegas_expected_success_probability_lb
    field_simp [hp0q]
  have hexpected :
      xi_hankel_finitefield_random_completion_las_vegas_expected_trials_bound (p := p) =
        (p : ℚ) / ((p : ℚ) - 1) := by
    rw [xi_hankel_finitefield_random_completion_las_vegas_expected_trials_bound, hsuccess]
    field_simp [show ((p : ℚ) - 1) ≠ 0 by linarith]
  have hbound :
      xi_hankel_finitefield_random_completion_las_vegas_expected_trials_bound (p := p) ≤ 2 := by
    rw [hexpected]
    have hp2 : (2 : ℚ) ≤ p := by
      exact_mod_cast hp.two_le
    have hpden_ge_one : (1 : ℚ) ≤ (p : ℚ) - 1 := by
      linarith
    have hinv_le_one : 1 / ((p : ℚ) - 1) ≤ 1 := by
      have h :=
        one_div_le_one_div_of_le (show (0 : ℚ) < 1 by norm_num) hpden_ge_one
      simpa using h
    have hrewrite : (p : ℚ) / ((p : ℚ) - 1) = 1 + 1 / ((p : ℚ) - 1) := by
      field_simp [show ((p : ℚ) - 1) ≠ 0 by linarith]
      ring
    rw [hrewrite]
    linarith
  exact ⟨hbase.1, hbase.2, hsuccess, hexpected, hbound⟩

end Omega.Zeta
