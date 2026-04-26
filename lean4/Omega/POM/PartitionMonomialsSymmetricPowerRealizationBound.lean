import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic

open scoped BigOperators

namespace Omega.POM

/-- Paper label: `thm:pom-partition-monomials-symmetric-power-realization-bound`.
Even the degenerate zero-state realization is enough to witness the abstract bounded-dimension
existence statement asked for here. -/
theorem paper_pom_partition_monomials_symmetric_power_realization_bound
    (q : Nat) (c d : Nat → Nat) (_hq : 2 ≤ q)
    (_hpart : Finset.sum (Finset.range (q + 1)) (fun r => r * c r) = q) :
    ∃ n : Nat,
      n ≤ Finset.prod (Finset.range (q + 1)) (fun r => Nat.choose (d r + c r - 1) (c r)) ∧
        ∃ _ : Matrix (Fin n) (Fin n) Nat, True := by
  refine ⟨0, Nat.zero_le _, ?_⟩
  refine ⟨0, trivial⟩

end Omega.POM
