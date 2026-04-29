import Mathlib.Tactic
import Omega.Conclusion.Period3FiberFullLatticePartition

namespace Omega.Conclusion

/-- The signed top-to-bottom Möbius coefficient of the period-three fiber partition lattice. -/
def conclusion_period3_fiber_factorial_mobius_tail_top_coefficient (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ (2 ^ n - 1) * (Nat.factorial (2 ^ n - 1) : ℤ)

/-- The same coefficient written through the full-lattice package's factorial absolute value. -/
def conclusion_period3_fiber_factorial_mobius_tail_packaged_coefficient (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ (2 ^ n - 1) * (period3FiberPartitionTopMobiusAbs n : ℤ)

/-- Concrete statement for the factorial Möbius tail on the period-three fiber. -/
def conclusion_period3_fiber_factorial_mobius_tail_statement : Prop :=
  ∀ n : ℕ,
    conclusion_period3_fiber_factorial_mobius_tail_packaged_coefficient n =
        conclusion_period3_fiber_factorial_mobius_tail_top_coefficient n ∧
      period3FiberPartitionTopMobiusAbs n = Nat.factorial (2 ^ n - 1)

/-- Paper label: `thm:conclusion-period3-fiber-factorial-mobius-tail`. -/
theorem paper_conclusion_period3_fiber_factorial_mobius_tail :
    conclusion_period3_fiber_factorial_mobius_tail_statement := by
  intro n
  rcases paper_conclusion_period3_fiber_full_lattice_partition n with ⟨_, _, hmobius⟩
  refine ⟨?_, hmobius⟩
  simp [conclusion_period3_fiber_factorial_mobius_tail_packaged_coefficient,
    conclusion_period3_fiber_factorial_mobius_tail_top_coefficient, hmobius]

end Omega.Conclusion
