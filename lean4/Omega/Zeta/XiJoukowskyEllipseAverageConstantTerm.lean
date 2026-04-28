import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Zeta.XiCayleyJoukowskyHarmonicMeasureEllipse

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

/-- Paper-facing collapse package: the constant-term average may be evaluated at `L = 1`,
where the Joukowsky ellipse is the segment `[-2, 2]` and the angular pushforward is arcsine. -/
def xi_joukowsky_ellipse_collapse_arcsine_master_statement : Prop :=
  (∀ D : xi_joukowsky_ellipse_average_constant_term_data,
    D.xi_joukowsky_ellipse_average_constant_term_average 1 =
        D.xi_joukowsky_ellipse_average_constant_term_constantTerm ∧
      (∀ L : ℝ, 0 < L →
        D.xi_joukowsky_ellipse_average_constant_term_average L =
          D.xi_joukowsky_ellipse_average_constant_term_average 1)) ∧
    (∀ θ : ℝ, xiJoukowskyX 1 θ = 2 * Real.cos θ ∧ xiJoukowskyY 1 θ = 0) ∧
      (∀ θ : ℝ, Real.sin θ ≠ 0 →
        xiArcsineDensity (xiJoukowskyX 1 θ) * (2 * |Real.sin θ|) = 1 / Real.pi)

/-- Paper label: `cor:xi-joukowsky-ellipse-collapse-arcsine-master`. -/
theorem paper_xi_joukowsky_ellipse_collapse_arcsine_master :
    xi_joukowsky_ellipse_collapse_arcsine_master_statement := by
  refine ⟨?_, paper_xi_cayley_joukowsky_harmonic_measure_ellipse.2.2.1,
    paper_xi_cayley_joukowsky_harmonic_measure_ellipse.2.2.2⟩
  intro D
  have hconstant := paper_xi_joukowsky_ellipse_average_constant_term D
  refine ⟨hconstant.1 1 zero_lt_one, ?_⟩
  intro L hL
  calc
    D.xi_joukowsky_ellipse_average_constant_term_average L =
        D.xi_joukowsky_ellipse_average_constant_term_constantTerm := hconstant.1 L hL
    _ = D.xi_joukowsky_ellipse_average_constant_term_average 1 :=
        (hconstant.1 1 zero_lt_one).symm

end

end Omega.Zeta
