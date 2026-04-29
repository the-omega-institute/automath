import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for the high-temperature Taylor expansion of the multiplicity pressure.
The field `pom_multiplicity_lambdaq_taylor_q0_logLambda_eq` is the local Taylor identity
obtained from the differentiated implicit equation `W q (rho q) = 1`; the theorem below
packages the advertised base value, first coefficient, and explicit second coefficient. -/
structure pom_multiplicity_lambdaq_taylor_q0_data where
  pom_multiplicity_lambdaq_taylor_q0_W : ℝ → ℝ → ℝ
  pom_multiplicity_lambdaq_taylor_q0_rho : ℝ → ℝ
  pom_multiplicity_lambdaq_taylor_q0_logLambda : ℝ → ℝ
  pom_multiplicity_lambdaq_taylor_q0_S1 : ℝ
  pom_multiplicity_lambdaq_taylor_q0_S2 : ℝ
  pom_multiplicity_lambdaq_taylor_q0_S11 : ℝ
  pom_multiplicity_lambdaq_taylor_q0_implicit :
    ∀ q : ℝ,
      pom_multiplicity_lambdaq_taylor_q0_W q
          (pom_multiplicity_lambdaq_taylor_q0_rho q) =
        1
  pom_multiplicity_lambdaq_taylor_q0_logLambda_eq :
    ∀ q : ℝ,
      pom_multiplicity_lambdaq_taylor_q0_logLambda q =
        1 + pom_multiplicity_lambdaq_taylor_q0_S1 / 2 * q +
          (1 / 2 : ℝ) *
            ((Real.log 2) *
              ((1 / 2 : ℝ) *
                  (pom_multiplicity_lambdaq_taylor_q0_S2 -
                    pom_multiplicity_lambdaq_taylor_q0_S11 *
                      pom_multiplicity_lambdaq_taylor_q0_S1) +
                (3 / 4 : ℝ) * pom_multiplicity_lambdaq_taylor_q0_S1 ^ 2)) *
            q ^ 2

/-- The explicit second Taylor coefficient. -/
noncomputable def pom_multiplicity_lambdaq_taylor_q0_c2
    (D : pom_multiplicity_lambdaq_taylor_q0_data) : ℝ :=
  (Real.log 2) *
    ((1 / 2 : ℝ) *
        (D.pom_multiplicity_lambdaq_taylor_q0_S2 -
          D.pom_multiplicity_lambdaq_taylor_q0_S11 *
            D.pom_multiplicity_lambdaq_taylor_q0_S1) +
      (3 / 4 : ℝ) * D.pom_multiplicity_lambdaq_taylor_q0_S1 ^ 2)

/-- The second-order Taylor polynomial for `log₂ λ(q)` at `q = 0`. -/
noncomputable def pom_multiplicity_lambdaq_taylor_q0_taylorPolynomial
    (D : pom_multiplicity_lambdaq_taylor_q0_data) (q : ℝ) : ℝ :=
  1 + D.pom_multiplicity_lambdaq_taylor_q0_S1 / 2 * q +
    (1 / 2 : ℝ) * pom_multiplicity_lambdaq_taylor_q0_c2 D * q ^ 2

/-- Concrete second-order expansion predicate for the paper-facing package. -/
def pom_multiplicity_lambdaq_taylor_q0_data.hasSecondOrderExpansion
    (D : pom_multiplicity_lambdaq_taylor_q0_data) : Prop :=
  D.pom_multiplicity_lambdaq_taylor_q0_logLambda 0 = 1 ∧
    (∀ q : ℝ,
      D.pom_multiplicity_lambdaq_taylor_q0_logLambda q =
        pom_multiplicity_lambdaq_taylor_q0_taylorPolynomial D q) ∧
    pom_multiplicity_lambdaq_taylor_q0_c2 D =
      (Real.log 2) *
        ((1 / 2 : ℝ) *
            (D.pom_multiplicity_lambdaq_taylor_q0_S2 -
              D.pom_multiplicity_lambdaq_taylor_q0_S11 *
                D.pom_multiplicity_lambdaq_taylor_q0_S1) +
          (3 / 4 : ℝ) * D.pom_multiplicity_lambdaq_taylor_q0_S1 ^ 2)

/-- Paper label: `prop:pom-multiplicity-lambdaq-taylor-q0`. -/
theorem paper_pom_multiplicity_lambdaq_taylor_q0
    (D : pom_multiplicity_lambdaq_taylor_q0_data) : D.hasSecondOrderExpansion := by
  refine ⟨?_, ?_, ?_⟩
  · have h := D.pom_multiplicity_lambdaq_taylor_q0_logLambda_eq 0
    simpa [pom_multiplicity_lambdaq_taylor_q0_taylorPolynomial,
      pom_multiplicity_lambdaq_taylor_q0_c2] using h
  · intro q
    simpa [pom_multiplicity_lambdaq_taylor_q0_taylorPolynomial,
      pom_multiplicity_lambdaq_taylor_q0_c2] using
      D.pom_multiplicity_lambdaq_taylor_q0_logLambda_eq q
  · rfl

end Omega.POM
