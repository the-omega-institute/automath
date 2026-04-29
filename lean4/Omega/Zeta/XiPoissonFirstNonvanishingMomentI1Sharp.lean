import Mathlib.Tactic
import Omega.Zeta.XiPoissonFirstNonvanishingMomentTvKlSharp

namespace Omega.Zeta

noncomputable section

/-- The derivative-exponent multiplier which transfers the KL leading constant to the `I_1`
leading constant at the first nonvanishing moment. -/
def xi_poisson_first_nonvanishing_moment_i1_sharp_derivativeExponentMultiplier
    (D : xi_poisson_first_nonvanishing_moment_tv_kl_sharp_data) : ℝ :=
  D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m

/-- Closed `I_1` leading constant, obtained from the verified KL constant by multiplying by the
first nonvanishing derivative exponent. -/
def xi_poisson_first_nonvanishing_moment_i1_sharp_leadingConstant
    (D : xi_poisson_first_nonvanishing_moment_tv_kl_sharp_data) : ℝ :=
  xi_poisson_first_nonvanishing_moment_i1_sharp_derivativeExponentMultiplier D *
    xi_poisson_first_nonvanishing_moment_tv_kl_sharp_kl_closed_constant D

/-- Fully expanded closed form for the sharp `I_1` leading constant. -/
def xi_poisson_first_nonvanishing_moment_i1_sharp_closedConstant
    (D : xi_poisson_first_nonvanishing_moment_tv_kl_sharp_data) : ℝ :=
  (D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ) *
    (D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_moment ^ 2 /
      (Nat.factorial D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ) ^ 2 *
        ((D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m : ℝ) *
          (Nat.factorial (2 * D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m) : ℝ) /
            (((2 * D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m - 1 : ℕ) : ℝ) *
              2 ^ (2 * D.xi_poisson_first_nonvanishing_moment_tv_kl_sharp_m + 1))))

/-- Paper-facing sharp `I_1` first-nonvanishing-moment statement. -/
def xi_poisson_first_nonvanishing_moment_i1_sharp_statement
    (D : xi_poisson_first_nonvanishing_moment_tv_kl_sharp_data) : Prop :=
  xi_poisson_first_nonvanishing_moment_i1_sharp_leadingConstant D =
      xi_poisson_first_nonvanishing_moment_i1_sharp_derivativeExponentMultiplier D *
        xi_poisson_first_nonvanishing_moment_tv_kl_sharp_kl_closed_constant D ∧
    xi_poisson_first_nonvanishing_moment_i1_sharp_leadingConstant D =
      xi_poisson_first_nonvanishing_moment_i1_sharp_closedConstant D

/-- Paper label: `cor:xi-poisson-first-nonvanishing-moment-i1-sharp`. -/
theorem paper_xi_poisson_first_nonvanishing_moment_i1_sharp
    (D : xi_poisson_first_nonvanishing_moment_tv_kl_sharp_data) :
    xi_poisson_first_nonvanishing_moment_i1_sharp_statement D := by
  constructor
  · rfl
  · rw [xi_poisson_first_nonvanishing_moment_i1_sharp_leadingConstant,
      xi_poisson_first_nonvanishing_moment_i1_sharp_derivativeExponentMultiplier,
      xi_poisson_first_nonvanishing_moment_i1_sharp_closedConstant,
      xi_poisson_first_nonvanishing_moment_tv_kl_sharp_kl_closed_constant]

end

end Omega.Zeta
