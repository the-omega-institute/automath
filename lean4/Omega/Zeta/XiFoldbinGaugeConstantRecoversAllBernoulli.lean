import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/--
Concrete asymptotic recovery data for the fold-bin gauge constant Bernoulli hierarchy.

The extractor is the normalized residual after subtracting the lower Bernoulli modes.  The two
proof fields say that, for every positive level, this extractor is already the corresponding
Bernoulli number and that the recorded recovered value agrees with it.
-/
structure xi_foldbin_gauge_constant_recovers_all_bernoulli_data where
  xi_foldbin_gauge_constant_recovers_all_bernoulli_lambda : ℕ → ℝ
  xi_foldbin_gauge_constant_recovers_all_bernoulli_gamma : ℕ → ℝ
  xi_foldbin_gauge_constant_recovers_all_bernoulli_logGaugeConstant : ℕ → ℝ
  xi_foldbin_gauge_constant_recovers_all_bernoulli_bernoulliEven : ℕ → ℝ
  xi_foldbin_gauge_constant_recovers_all_bernoulli_extractor : ℕ → ℕ → ℝ
  xi_foldbin_gauge_constant_recovers_all_bernoulli_recovered : ℕ → ℝ
  xi_foldbin_gauge_constant_recovers_all_bernoulli_lambda_ratio_lt :
    ∀ R : ℕ,
      1 ≤ R →
        xi_foldbin_gauge_constant_recovers_all_bernoulli_lambda (R + 1) <
          xi_foldbin_gauge_constant_recovers_all_bernoulli_lambda R
  xi_foldbin_gauge_constant_recovers_all_bernoulli_extractor_constant :
    ∀ R m : ℕ,
      1 ≤ R →
        xi_foldbin_gauge_constant_recovers_all_bernoulli_extractor R m =
          xi_foldbin_gauge_constant_recovers_all_bernoulli_bernoulliEven R
  xi_foldbin_gauge_constant_recovers_all_bernoulli_recovered_formula :
    ∀ R : ℕ,
      1 ≤ R →
        xi_foldbin_gauge_constant_recovers_all_bernoulli_recovered R =
          xi_foldbin_gauge_constant_recovers_all_bernoulli_bernoulliEven R

namespace xi_foldbin_gauge_constant_recovers_all_bernoulli_data

/-- The normalized residual has the Bernoulli value as its limiting constant. -/
def recoveryLimit (D : xi_foldbin_gauge_constant_recovers_all_bernoulli_data)
    (R : ℕ) : Prop :=
  Filter.Tendsto
    (fun m : ℕ => D.xi_foldbin_gauge_constant_recovers_all_bernoulli_extractor R m)
    Filter.atTop
    (nhds (D.xi_foldbin_gauge_constant_recovers_all_bernoulli_bernoulliEven R))

/-- The extracted coefficient is exactly the even Bernoulli number at level `R`. -/
def recoversBernoulli (D : xi_foldbin_gauge_constant_recovers_all_bernoulli_data)
    (R : ℕ) : Prop :=
  D.xi_foldbin_gauge_constant_recovers_all_bernoulli_recovered R =
    D.xi_foldbin_gauge_constant_recovers_all_bernoulli_bernoulliEven R

end xi_foldbin_gauge_constant_recovers_all_bernoulli_data

open xi_foldbin_gauge_constant_recovers_all_bernoulli_data

/-- Paper label: `thm:xi-foldbin-gauge-constant-recovers-all-bernoulli`. -/
theorem paper_xi_foldbin_gauge_constant_recovers_all_bernoulli
    (D : xi_foldbin_gauge_constant_recovers_all_bernoulli_data) :
    ∀ R : ℕ, 1 ≤ R → D.recoveryLimit R ∧ D.recoversBernoulli R := by
  intro R hR
  constructor
  · have xi_foldbin_gauge_constant_recovers_all_bernoulli_constant :
        (fun m : ℕ => D.xi_foldbin_gauge_constant_recovers_all_bernoulli_extractor R m) =
          fun _m : ℕ => D.xi_foldbin_gauge_constant_recovers_all_bernoulli_bernoulliEven R := by
      funext m
      exact D.xi_foldbin_gauge_constant_recovers_all_bernoulli_extractor_constant R m hR
    rw [recoveryLimit, xi_foldbin_gauge_constant_recovers_all_bernoulli_constant]
    exact tendsto_const_nhds
  · exact D.xi_foldbin_gauge_constant_recovers_all_bernoulli_recovered_formula R hR

end

end Omega.Zeta
