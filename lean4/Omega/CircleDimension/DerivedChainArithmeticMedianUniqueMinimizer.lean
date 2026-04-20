import Mathlib.Tactic
import Omega.CircleDimension.SquarefreeMedianDistance
import Omega.CircleDimension.SquarefreeMedianMetricEllipseRealization

namespace Omega.CircleDimension

/-- The concrete squarefree chain used to witness the derived arithmetic median statement. -/
def derivedChainArithmeticCarrier : Finset ℕ :=
  {1, 2, 3, 5, 6, 10, 15, 30}

/-- Three-point support-distance objective for the squarefree chain witness. -/
def derivedChainArithmeticObjective (n : ℕ) : ℕ :=
  squarefreeSupportDistance n 6 + squarefreeSupportDistance n 10 + squarefreeSupportDistance n 15

/-- The same objective transported to the ellipse realization. -/
def derivedChainEllipseObjective (E : SquarefreeEllipse) : ℕ :=
  derivedChainArithmeticObjective E

/-- Concrete derived-chain median package: the gcd closed form gives the median `30` for the
triple `(6, 10, 15)`, and this point is the unique minimizer of the corresponding three-point
support-distance sum on the associated squarefree ellipse family.
    thm:derived-chain-arithmetic-median-unique-minimizer -/
theorem paper_derived_chain_arithmetic_median_unique_minimizer :
    squarefreeMedianCenter 6 10 15 = 30 ∧
    squarefreeEllipseMedian (squarefreeEllipseOf 6) (squarefreeEllipseOf 10)
        (squarefreeEllipseOf 15) = squarefreeEllipseOf 30 ∧
    (∀ n ∈ derivedChainArithmeticCarrier,
      derivedChainArithmeticObjective 30 ≤ derivedChainArithmeticObjective n) ∧
    (∀ E ∈ derivedChainArithmeticCarrier.image squarefreeEllipseOf,
      derivedChainEllipseObjective (squarefreeEllipseOf 30) ≤ derivedChainEllipseObjective E) ∧
    (∀ E ∈ derivedChainArithmeticCarrier.image squarefreeEllipseOf,
      derivedChainEllipseObjective E = derivedChainEllipseObjective (squarefreeEllipseOf 30) →
        E = squarefreeEllipseOf 30) := by
  native_decide

end Omega.CircleDimension
