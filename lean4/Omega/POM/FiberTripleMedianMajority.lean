import Mathlib.Tactic

/-!
# Majority seed for the fiber triple median

This file registers the paper-facing seed/package wrapper for
`thm:pom-fiber-triple-median-majority`.
-/

namespace Omega.POM.FiberTripleMedianMajority

/-- Boolean majority on three inputs. -/
def majority3 (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- The Boolean majority minimizes the three-point Hamming cost. -/
theorem majority3_minimizes_hamming (a b c t : Bool) :
    (if majority3 a b c ≠ a then 1 else 0) +
      (if majority3 a b c ≠ b then 1 else 0) +
      (if majority3 a b c ≠ c then 1 else 0) ≤
    (if t ≠ a then 1 else 0) +
      (if t ≠ b then 1 else 0) +
      (if t ≠ c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> cases t <;> decide

/-- Paper seed for the triple-median majority formula.
    thm:pom-fiber-triple-median-majority -/
theorem paper_pom_fiber_triple_median_majority_seeds (a b c t : Bool) :
    (if majority3 a b c ≠ a then 1 else 0) +
      (if majority3 a b c ≠ b then 1 else 0) +
      (if majority3 a b c ≠ c then 1 else 0) ≤
    (if t ≠ a then 1 else 0) +
      (if t ≠ b then 1 else 0) +
      (if t ≠ c then 1 else 0) :=
  majority3_minimizes_hamming a b c t

/-- Packaged form of the triple-median majority formula.
    thm:pom-fiber-triple-median-majority -/
theorem paper_pom_fiber_triple_median_majority_package (a b c t : Bool) :
    (if majority3 a b c ≠ a then 1 else 0) +
      (if majority3 a b c ≠ b then 1 else 0) +
      (if majority3 a b c ≠ c then 1 else 0) ≤
    (if t ≠ a then 1 else 0) +
      (if t ≠ b then 1 else 0) +
      (if t ≠ c then 1 else 0) :=
  paper_pom_fiber_triple_median_majority_seeds a b c t

end Omega.POM.FiberTripleMedianMajority
