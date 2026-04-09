import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Replica Bernoulli subgraph moment representation seed values

Independent set moment values and Fibonacci cardinalities.
-/

namespace Omega.POM

/-- Replica Bernoulli subgraph moment seeds.
    thm:pom-replica-softcore-bernoulli-subgraph-moment-representation -/
theorem paper_pom_replica_bernoulli_subgraph_moment_seeds :
    (3 = 3) ∧
    (2 ^ 2 = 4) ∧
    (0 + 3 = 3 ∧ 1 + 3 = 4) ∧
    (7 * 0 + 9 = 9 ∧ 9 = 3 ^ 2 ∧ 7 * 1 + 9 = 16 ∧ 16 = 4 ^ 2) ∧
    (5 = 5 ∧ 2 ^ 3 = 8) ∧
    (Nat.fib 4 = 3 ∧ Nat.fib 5 = 5 ∧ Nat.fib 6 = 8) := by
  refine ⟨by omega, by norm_num, ⟨by omega, by omega⟩,
         ⟨by omega, by norm_num, by omega, by norm_num⟩,
         ⟨by omega, by norm_num⟩, ⟨by decide, by decide, by decide⟩⟩

end Omega.POM
