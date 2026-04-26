import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.Period3FiberExactMultiplicity
import Omega.Folding.IntermediateQuotientsBellProductDoubleExponential

namespace Omega.Conclusion

open Omega.Conclusion.Period3FiberExactMultiplicity

/-- Bell-type count contributed by the full intermediate quotient lattice on the period-`3`
fiber. -/
def period3FiberFullPartitionCount (n : ℕ) : ℕ :=
  Omega.Folding.fiberBellChoices (Fintype.card (Period3FiberBlockChoices n))

/-- Absolute value of the top Möbius coefficient for the partition lattice on the period-`3`
fiber. -/
def period3FiberPartitionTopMobiusAbs (n : ℕ) : ℕ :=
  Nat.factorial (Fintype.card (Period3FiberBlockChoices n) - 1)

/-- Concrete period-`3` full-lattice partition package: the fiber has cardinality `2^n`, the
Bell-type intermediate quotient count is evaluated on that fiber size, and the top Möbius
coefficient has the standard factorial absolute value. -/
def Period3FiberFullLatticePartition (n : ℕ) : Prop :=
  Fintype.card (Period3FiberBlockChoices n) = 2 ^ n ∧
    period3FiberFullPartitionCount n = Omega.Folding.fiberBellChoices (2 ^ n) ∧
    period3FiberPartitionTopMobiusAbs n = Nat.factorial (2 ^ n - 1)

/-- Paper label: `thm:conclusion-period3-fiber-full-lattice-partition`. The exact multiplicity
`|F_n| = 2^n` identifies the period-`3` fiber with a finite set of size `2^n`, so the single-fiber
Bell proxy and the top Möbius factorial take their standard partition-lattice forms. -/
theorem paper_conclusion_period3_fiber_full_lattice_partition (n : ℕ) :
    Period3FiberFullLatticePartition n := by
  have hCube := paper_conclusion_period3_fiber_hypercube_vc n
  have hcard : Fintype.card (Period3FiberBlockChoices n) = 2 ^ n := by
    exact hCube.2.2.1
  refine ⟨hcard, ?_, ?_⟩
  · simp [period3FiberFullPartitionCount, hcard]
  · simp [period3FiberPartitionTopMobiusAbs, hcard]

end Omega.Conclusion
