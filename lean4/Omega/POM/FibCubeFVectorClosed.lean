import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- Paper-facing package of the Fibonacci-cube f-vector recurrence together with its vanishing
range and positivity window.
    thm:pom-fibcube-fvector-closed -/
theorem paper_pom_fibcube_fvector_closed (n k : Nat) :
    Omega.fibcubeFVector (n + 2) k =
        Omega.fibcubeFVector (n + 1) k + Omega.fibcubeFVector n k +
          (if k = 0 then 0 else Omega.fibcubeFVector n (k - 1)) ∧
      (((n + 1) / 2 < k) → Omega.fibcubeFVector n k = 0) ∧
      ((2 * k ≤ n) → 0 < Omega.fibcubeFVector n k) := by
  refine ⟨Omega.fibcubeFVector_succ_succ n k, ?_, ?_⟩
  · intro hk
    exact Omega.fibcubeFVector_eq_zero_of_gt n k hk
  · intro hk
    exact Omega.fibcubeFVector_pos n k hk

end Omega.POM
