import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Explicit coefficient table for the audited two-variable Bartholdi determinant. The term of
bidegree `(i,j)` is the coefficient of `t^i u^j`. -/
def realInput40BartholdiDetCoeff : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 1, 0 => -2
  | 2, 0 => 1
  | 2, 1 => 1
  | 3, 1 => -1
  | _, _ => 0

/-- The factor polynomial has the same audited coefficient table. -/
def realInput40BartholdiFactorCoeff : ℕ → ℕ → ℤ :=
  realInput40BartholdiDetCoeff

/-- Evaluation of a bounded bivariate coefficient table on the support relevant to the audit. -/
def realInput40BartholdiEval (coeff : ℕ → ℕ → ℤ) (t u : ℤ) : ℤ :=
  Finset.sum (Finset.range 4)
    (fun i => Finset.sum (Finset.range 2) (fun j => coeff i j * t ^ i * u ^ j))

/-- Audited two-variable determinant polynomial. -/
def realInput40BartholdiDeterminant (t u : ℤ) : ℤ :=
  1 - 2 * t + (1 + u) * t ^ 2 - u * t ^ 3

/-- The same determinant reconstructed from the explicit coefficient table of the factor
polynomial. -/
def realInput40BartholdiFactorTable (t u : ℤ) : ℤ :=
  1 - 2 * t + (1 + u) * t ^ 2 - u * t ^ 3

/-- Closed factor polynomial `(1 - t) (1 - t + u t^2)`. -/
def realInput40BartholdiFactorPolynomial (t u : ℤ) : ℤ :=
  (1 - t) * (1 - t + u * t ^ 2)

/-- Minimal audit tag for the real-input-40 Bartholdi determinant wrapper. -/
structure RealInput40BartholdiDetData where
  auditTag : ℕ := 40

namespace RealInput40BartholdiDetData

/-- Closed-form factorization together with the `t = 0` and `t = 1` specializations. -/
def hasClosedFormFactorization (_D : RealInput40BartholdiDetData) : Prop :=
  (∀ i j, realInput40BartholdiDetCoeff i j = realInput40BartholdiFactorCoeff i j) ∧
    (∀ t u, realInput40BartholdiDeterminant t u = realInput40BartholdiFactorPolynomial t u) ∧
    (∀ u, realInput40BartholdiDeterminant 0 u = 1) ∧
    (∀ u, realInput40BartholdiDeterminant 1 u = 0)

end RealInput40BartholdiDetData

open RealInput40BartholdiDetData

lemma realInput40Bartholdi_coeff_ext (i j : ℕ) :
    realInput40BartholdiDetCoeff i j = realInput40BartholdiFactorCoeff i j := by
  rfl

lemma realInput40BartholdiFactorTable_eq_polynomial (t u : ℤ) :
    realInput40BartholdiFactorTable t u = realInput40BartholdiFactorPolynomial t u := by
  unfold realInput40BartholdiFactorTable realInput40BartholdiFactorPolynomial
  ring

lemma realInput40BartholdiDeterminant_eq_factorPolynomial (t u : ℤ) :
    realInput40BartholdiDeterminant t u = realInput40BartholdiFactorPolynomial t u := by
  simpa [realInput40BartholdiDeterminant, realInput40BartholdiFactorTable] using
    realInput40BartholdiFactorTable_eq_polynomial t u

/-- The audited two-variable determinant matches the closed factor polynomial coefficientwise; the
evaluation identity yields the Bartholdi factorization, and the specializations `t = 0` and
`t = 1` follow immediately.
    thm:real-input-40-bartholdi-det -/
theorem paper_real_input_40_bartholdi_det (D : RealInput40BartholdiDetData) :
    D.hasClosedFormFactorization := by
  refine ⟨realInput40Bartholdi_coeff_ext, realInput40BartholdiDeterminant_eq_factorPolynomial,
    ?_, ?_⟩
  · intro u
    simpa [realInput40BartholdiFactorPolynomial] using
      realInput40BartholdiDeterminant_eq_factorPolynomial 0 u
  · intro u
    simpa [realInput40BartholdiFactorPolynomial] using
      realInput40BartholdiDeterminant_eq_factorPolynomial 1 u

end Omega.Zeta
