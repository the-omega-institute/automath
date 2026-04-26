import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmEllipticFiberCountMeanTrace

namespace Omega.Zeta

open scoped BigOperators

/-- The uniform single-sample mean of the centered fiber count `Z = N_p(Y) - 1`. -/
def xi_terminal_zm_elliptic_mc_trace_estimator_uniform_mean
    (p : ℕ) (N_p : Fin p → ℕ) : ℚ :=
  (∑ y : Fin p, ((N_p y : ℚ) - 1)) / p

/-- The Monte Carlo trace estimator `\hat a_p = -p \bar Z`. -/
def xi_terminal_zm_elliptic_mc_trace_estimator_hat
    (p : ℕ) (_n : ℕ) (sampleMean : ℚ) : ℚ :=
  -(p : ℚ) * sampleMean

/-- The variance of one centered sample under the uniform law on `𝔽_p`, written as a finite
average. -/
def xi_terminal_zm_elliptic_mc_trace_estimator_single_sample_variance
    (p : ℕ) (N_p : Fin p → ℕ) : ℚ :=
  let μ := xi_terminal_zm_elliptic_mc_trace_estimator_uniform_mean p N_p
  (∑ y : Fin p, (((N_p y : ℚ) - 1) - μ) ^ 2) / p

/-- The iid sample-mean variance formula specialized to `\hat a_p = -p \bar Z`. -/
def xi_terminal_zm_elliptic_mc_trace_estimator_estimator_variance
    (p n : ℕ) (N_p : Fin p → ℕ) : ℚ :=
  ((p : ℚ) ^ 2 / n) *
    xi_terminal_zm_elliptic_mc_trace_estimator_single_sample_variance p N_p

/-- Paper label: `cor:xi-terminal-zm-elliptic-mc-trace-estimator`. The preceding mean-trace
identity computes the centered uniform mean `E[Z_1] = -a_p / p`; multiplying by `-p` makes the
Monte Carlo estimator unbiased, and the variance package is exactly the standard iid scaling
`p^2/n · Var(Z_1)`. -/
theorem paper_xi_terminal_zm_elliptic_mc_trace_estimator :
    ∀ {p n : ℕ} (hp : 0 < p) (_hn : 0 < n) (a_p : Int) (N_p : Fin p → ℕ),
      (∑ y : Fin p, (N_p y : Int)) = (p : Int) - a_p →
      let μ := xi_terminal_zm_elliptic_mc_trace_estimator_uniform_mean p N_p
      let ahat := xi_terminal_zm_elliptic_mc_trace_estimator_hat p n μ
      μ = -(a_p : ℚ) / p ∧
        ahat = a_p ∧
        xi_terminal_zm_elliptic_mc_trace_estimator_estimator_variance p n N_p =
          ((p : ℚ) ^ 2 / n) *
            xi_terminal_zm_elliptic_mc_trace_estimator_single_sample_variance p N_p := by
  intro p n hp hn a_p N_p hcount
  let μ := xi_terminal_zm_elliptic_mc_trace_estimator_uniform_mean p N_p
  let ahat := xi_terminal_zm_elliptic_mc_trace_estimator_hat p n μ
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hp
  have hmean_int :
      (∑ y : Fin p, ((N_p y : Int) - 1)) = -a_p :=
    paper_xi_terminal_zm_elliptic_fiber_count_mean_trace p a_p N_p hcount
  have hmean_rat :
      (∑ y : Fin p, ((N_p y : ℚ) - 1)) = -(a_p : ℚ) := by
    exact_mod_cast hmean_int
  have hμ : μ = -(a_p : ℚ) / p := by
    unfold μ xi_terminal_zm_elliptic_mc_trace_estimator_uniform_mean
    rw [hmean_rat]
  have hhat : ahat = a_p := by
    unfold ahat xi_terminal_zm_elliptic_mc_trace_estimator_hat
    rw [hμ]
    field_simp [hpq]
  refine ⟨hμ, hhat, rfl⟩

end Omega.Zeta
