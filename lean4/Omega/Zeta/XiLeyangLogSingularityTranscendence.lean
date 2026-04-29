import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete algebraic logarithm package for the Lee--Yang singular value.  The final field is
the local Lindemann--Weierstrass input specialized to the chosen logarithm. -/
structure xi_leyang_log_singularity_transcendence_data where
  xi_leyang_log_singularity_transcendence_yStar : ℂ
  xi_leyang_log_singularity_transcendence_sStar : ℂ
  xi_leyang_log_singularity_transcendence_yStar_algebraic :
    IsAlgebraic ℚ xi_leyang_log_singularity_transcendence_yStar
  xi_leyang_log_singularity_transcendence_yStar_ne_zero :
    xi_leyang_log_singularity_transcendence_yStar ≠ 0
  xi_leyang_log_singularity_transcendence_yStar_ne_one :
    xi_leyang_log_singularity_transcendence_yStar ≠ 1
  xi_leyang_log_singularity_transcendence_exp_sStar :
    Complex.exp xi_leyang_log_singularity_transcendence_sStar =
      xi_leyang_log_singularity_transcendence_yStar
  xi_leyang_log_singularity_transcendence_exp_transcendental_of_nonzero_algebraic_log :
    IsAlgebraic ℚ xi_leyang_log_singularity_transcendence_sStar →
      xi_leyang_log_singularity_transcendence_sStar ≠ 0 →
        ¬ IsAlgebraic ℚ (Complex.exp xi_leyang_log_singularity_transcendence_sStar)

namespace xi_leyang_log_singularity_transcendence_data

/-- The logarithm of the algebraic branch value is not algebraic. -/
def statement (D : xi_leyang_log_singularity_transcendence_data) : Prop :=
  ¬ IsAlgebraic ℚ D.xi_leyang_log_singularity_transcendence_sStar

end xi_leyang_log_singularity_transcendence_data

/-- Paper label: `thm:xi-leyang-log-singularity-transcendence`. -/
theorem paper_xi_leyang_log_singularity_transcendence
    (D : xi_leyang_log_singularity_transcendence_data) : D.statement := by
  intro hs_alg
  by_cases hs_zero : D.xi_leyang_log_singularity_transcendence_sStar = 0
  · apply D.xi_leyang_log_singularity_transcendence_yStar_ne_one
    rw [← D.xi_leyang_log_singularity_transcendence_exp_sStar, hs_zero, Complex.exp_zero]
  · exact
      (D.xi_leyang_log_singularity_transcendence_exp_transcendental_of_nonzero_algebraic_log
        hs_alg hs_zero)
        (by
          rw [D.xi_leyang_log_singularity_transcendence_exp_sStar]
          exact D.xi_leyang_log_singularity_transcendence_yStar_algebraic)

end Omega.Zeta
