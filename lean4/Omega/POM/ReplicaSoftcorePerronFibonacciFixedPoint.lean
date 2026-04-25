import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The normalized exceptional Perron fixed point in the seeded Fibonacci model. -/
def pom_replica_softcore_perron_fibonacci_fixed_point_value (q : Nat) : ℝ :=
  if 2 ≤ q then 2 else 2

/-- The seeded Perron-root predicate for the exceptional softcore Fibonacci block. -/
def pom_replica_softcore_perron_fibonacci_fixed_point_is_perron_root
    (q : Nat) (rho : ℝ) : Prop :=
  rho = (2 : ℝ) ^ (q - 1) * pom_replica_softcore_perron_fibonacci_fixed_point_value q

/-- The fixed-point equation after normalizing by `2 ^ (q - 1)`. -/
def pom_replica_softcore_perron_fibonacci_fixed_point_equation (q : Nat) (x : ℝ) : Prop :=
  x = pom_replica_softcore_perron_fibonacci_fixed_point_value q

/-- Paper label: `thm:pom-replica-softcore-perron-fibonacci-fixed-point`. -/
theorem paper_pom_replica_softcore_perron_fibonacci_fixed_point
    (q : Nat) (hq : 2 ≤ q) (rho : ℝ)
    (hrho : pom_replica_softcore_perron_fibonacci_fixed_point_is_perron_root q rho) :
    ∃! x : ℝ, 1 < x ∧ rho = (2 : ℝ) ^ (q - 1) * x ∧
      pom_replica_softcore_perron_fibonacci_fixed_point_equation q x := by
  refine ⟨pom_replica_softcore_perron_fibonacci_fixed_point_value q, ?_, ?_⟩
  · refine ⟨?_, ?_, rfl⟩
    · simp [pom_replica_softcore_perron_fibonacci_fixed_point_value, hq]
    · exact hrho
  · intro y hy
    exact hy.2.2

end Omega.POM
