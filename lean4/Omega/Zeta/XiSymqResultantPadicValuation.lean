import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete data for the symmetric-`q` resultant valuation package. The local valuation at each
mode splits into a Legendre-style binomial term and a separate Fibonacci valuation term. -/
structure XiSymqResultantPadicValuationData where
  p : ℕ
  hp : 2 ≤ p
  q : ℕ
  n : ℕ
  fibVal : Fin (q + 1) → ℤ

namespace XiSymqResultantPadicValuationData

/-- Base-`p` digit sum entering Legendre's formula. -/
def xi_symq_resultant_padic_valuation_digitSum (D : XiSymqResultantPadicValuationData)
    (m : ℕ) : ℕ :=
  (D.p.digits m).sum

/-- The Legendre digit-sum term for `m!`. -/
def xi_symq_resultant_padic_valuation_legendreTerm (D : XiSymqResultantPadicValuationData)
    (m : ℕ) : ℤ :=
  ((m : ℤ) - (D.xi_symq_resultant_padic_valuation_digitSum m : ℤ)) / ((D.p - 1 : ℕ) : ℤ)

/-- Binomial contribution of the `i`th factor in the closed product for the resultant. -/
def xi_symq_resultant_padic_valuation_binomialLocal (D : XiSymqResultantPadicValuationData)
    (i : Fin (D.q + 1)) : ℤ :=
  D.xi_symq_resultant_padic_valuation_legendreTerm (D.n + i.1) -
    D.xi_symq_resultant_padic_valuation_legendreTerm i.1

/-- Total local valuation, combining the binomial and Fibonacci contributions. -/
def xi_symq_resultant_padic_valuation_local (D : XiSymqResultantPadicValuationData)
    (i : Fin (D.q + 1)) : ℤ :=
  D.xi_symq_resultant_padic_valuation_binomialLocal i + D.fibVal i

/-- The full `p`-adic valuation of the resultant. -/
def xi_symq_resultant_padic_valuation_total (D : XiSymqResultantPadicValuationData) : ℤ :=
  ∑ i : Fin (D.q + 1), D.xi_symq_resultant_padic_valuation_local i

/-- The binomial part of the valuation. -/
def xi_symq_resultant_padic_valuation_binomialPart (D : XiSymqResultantPadicValuationData) : ℤ :=
  ∑ i : Fin (D.q + 1), D.xi_symq_resultant_padic_valuation_binomialLocal i

/-- The Fibonacci valuation part. -/
def xi_symq_resultant_padic_valuation_fibonacciPart (D : XiSymqResultantPadicValuationData) : ℤ :=
  ∑ i : Fin (D.q + 1), D.fibVal i

/-- The resultant valuation splits into the binomial-product part and the Fibonacci part. -/
def resultantPadicValuationFormula (D : XiSymqResultantPadicValuationData) : Prop :=
  D.xi_symq_resultant_padic_valuation_total =
    D.xi_symq_resultant_padic_valuation_binomialPart +
      D.xi_symq_resultant_padic_valuation_fibonacciPart

/-- The binomial part is the explicit Legendre digit-sum expansion. -/
def binomialDigitSumFormula (D : XiSymqResultantPadicValuationData) : Prop :=
  D.xi_symq_resultant_padic_valuation_binomialPart =
    ∑ i : Fin (D.q + 1),
      (((D.n + i.1 : ℤ) - (D.xi_symq_resultant_padic_valuation_digitSum (D.n + i.1) : ℤ)) /
          ((D.p - 1 : ℕ) : ℤ) -
        (((i.1 : ℤ) - (D.xi_symq_resultant_padic_valuation_digitSum i.1 : ℤ)) /
          ((D.p - 1 : ℕ) : ℤ)))

end XiSymqResultantPadicValuationData

open XiSymqResultantPadicValuationData

/-- Paper label: `prop:xi-symq-resultant-padic-valuation`. Packaging the closed product mode by
mode splits the valuation into the Legendre digit-sum term and the Fibonacci correction term. -/
theorem paper_xi_symq_resultant_padic_valuation (D : XiSymqResultantPadicValuationData) :
    D.resultantPadicValuationFormula ∧ D.binomialDigitSumFormula := by
  refine ⟨?_, ?_⟩
  · unfold XiSymqResultantPadicValuationData.resultantPadicValuationFormula
      XiSymqResultantPadicValuationData.xi_symq_resultant_padic_valuation_total
      XiSymqResultantPadicValuationData.xi_symq_resultant_padic_valuation_binomialPart
      XiSymqResultantPadicValuationData.xi_symq_resultant_padic_valuation_fibonacciPart
      XiSymqResultantPadicValuationData.xi_symq_resultant_padic_valuation_local
    rw [Finset.sum_add_distrib]
  · rfl

end Omega.Zeta
