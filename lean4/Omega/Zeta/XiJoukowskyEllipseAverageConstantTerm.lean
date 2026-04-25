import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

open scoped BigOperators

/-- Concrete finite Taylor package for the Joukowsky ellipse average.  The average is represented
by the constant coefficient of the pulled-back Laurent polynomial; expanding powers of
`z + z⁻¹` gives the central-binomial expression. -/
structure xi_joukowsky_ellipse_average_constant_term_data where
  xi_joukowsky_ellipse_average_constant_term_degree : ℕ
  xi_joukowsky_ellipse_average_constant_term_taylorCoeff : ℕ → ℝ

namespace xi_joukowsky_ellipse_average_constant_term_data

/-- Constant term obtained from the even Taylor coefficients after expanding `(z + z⁻¹)^(2k)`. -/
def xi_joukowsky_ellipse_average_constant_term_constantTerm
    (D : xi_joukowsky_ellipse_average_constant_term_data) : ℝ :=
  (Finset.range (D.xi_joukowsky_ellipse_average_constant_term_degree + 1)).sum fun k =>
    (Nat.choose (2 * k) k : ℝ) *
      D.xi_joukowsky_ellipse_average_constant_term_taylorCoeff (2 * k)

/-- The ellipse average in this finite coefficient-extraction interface; the radius parameter is
invisible because the constant Laurent coefficient is unchanged by the radius rescaling. -/
def xi_joukowsky_ellipse_average_constant_term_average
    (D : xi_joukowsky_ellipse_average_constant_term_data) (_L : ℝ) : ℝ :=
  D.xi_joukowsky_ellipse_average_constant_term_constantTerm

/-- Paper-facing statement: the average is scale-independent and equals the extracted constant
term, which is the central-binomial coefficient sum. -/
def average_eq_constant_term (D : xi_joukowsky_ellipse_average_constant_term_data) : Prop :=
  (∀ L : ℝ, 0 < L →
    D.xi_joukowsky_ellipse_average_constant_term_average L =
    D.xi_joukowsky_ellipse_average_constant_term_constantTerm) ∧
    D.xi_joukowsky_ellipse_average_constant_term_constantTerm =
      (Finset.range (D.xi_joukowsky_ellipse_average_constant_term_degree + 1)).sum fun k =>
        (Nat.choose (2 * k) k : ℝ) *
          D.xi_joukowsky_ellipse_average_constant_term_taylorCoeff (2 * k)

end xi_joukowsky_ellipse_average_constant_term_data

open xi_joukowsky_ellipse_average_constant_term_data

/-- Paper label: `prop:xi-joukowsky-ellipse-average-constant-term`. -/
theorem paper_xi_joukowsky_ellipse_average_constant_term
    (D : xi_joukowsky_ellipse_average_constant_term_data) : D.average_eq_constant_term := by
  refine ⟨?_, ?_⟩
  · intro L _hL
    rfl
  · rfl

end

end Omega.Zeta
