import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite-scale data for the hidden log-multiplicity pressure package.  The derivatives
are recorded as concrete `HasDerivAt` hypotheses for the displayed log-sum pressure and its first
derivative formula; the statement below converts them to `deriv` identities and keeps the
dimension-to-multiplicity logarithm rewrite explicit. -/
structure xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_data where
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_state : Type
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_fintype :
    Fintype xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_state
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_scale : ℕ
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_dimension :
    xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_state → ℝ
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_logMultiplicity :
    xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_state → ℝ
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_observable :
    xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_state → ℝ
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_dimension_pos :
    ∀ x : xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_state,
      0 < xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_dimension x
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_logMultiplicity_eq :
    ∀ x : xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_state,
      xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_logMultiplicity x =
        Real.log (xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_dimension x) -
          xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_scale * Real.log 2
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_first : ℝ → ℝ
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_second : ℝ → ℝ
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_limitSecond : ℝ → ℝ
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_pressure_hasDerivAt :
    ∀ q,
      HasDerivAt
        (fun u =>
          Real.log
            (∑ x,
              Real.exp
                (xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_logMultiplicity x +
                  u * xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_observable x)))
        (xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_first q) q
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_first_hasDerivAt :
    ∀ q,
      HasDerivAt xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_first
        (xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_second q) q
  xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_c2_local_convergence :
    ∀ q,
      xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_limitSecond q =
        xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_second q

namespace xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_data

/-- The finite log-sum pressure. -/
def xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_pressure
    (D : xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_data) (q : ℝ) : ℝ :=
  let _ := D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_fintype
  Real.log
    (∑ x,
      Real.exp
        (D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_logMultiplicity x +
          q * D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_observable x))

/-- The finite first derivative supplied by the finite pressure package. -/
def xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_pressureDerivative
    (D : xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_data) : ℝ → ℝ :=
  D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_first

/-- The finite second derivative supplied by the finite pressure package. -/
def xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_pressureSecondDerivative
    (D : xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_data) : ℝ → ℝ :=
  D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_second

/-- Paper-facing statement: log multiplicities rewrite as `log d - m log 2`, the two finite-scale
derivative identities hold as `deriv` equalities, and the local `C^2` limit has the same second
derivative. -/
def xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_statement
    (D : xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_data) : Prop :=
  (∀ x : D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_state,
    D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_logMultiplicity x =
      Real.log (D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_dimension x) -
        D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_scale * Real.log 2) ∧
    (∀ q,
      deriv D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_pressure q =
        D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_pressureDerivative q) ∧
      (∀ q,
        deriv D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_pressureDerivative q =
          D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_pressureSecondDerivative q) ∧
        (∀ q,
          D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_limitSecond q =
            D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_pressureSecondDerivative q)

end xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_data

open xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_data

/-- Paper label:
`thm:xi-time-part60ab-hidden-logmultiplicity-pressure-derivatives`. -/
theorem paper_xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives
    (D : xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_data) :
    xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_statement D := by
  let _ := D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_fintype
  refine ⟨D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_logMultiplicity_eq,
    ?_, ?_, ?_⟩
  · intro q
    exact
      (D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_pressure_hasDerivAt q).deriv
  · intro q
    exact
      (D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_first_hasDerivAt q).deriv
  · intro q
    exact D.xi_time_part60ab_hidden_logmultiplicity_pressure_derivatives_c2_local_convergence q

end

end Omega.Zeta
