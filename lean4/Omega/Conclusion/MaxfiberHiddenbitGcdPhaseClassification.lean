import Mathlib.Tactic
import Omega.Core.MaxFiberSplitGcdTrichotomy

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-maxfiber-hiddenbit-gcd-phase-classification`. -/
theorem paper_conclusion_maxfiber_hiddenbit_gcd_phase_classification :
    (∀ k : Nat, 5 <= k -> Nat.gcd (Nat.fib (k + 1)) (Nat.fib k) = 1) ∧
    (∀ k : Nat, 6 <= k ->
      Nat.gcd (Nat.fib (k + 1)) (Nat.fib (k + 1)) = Nat.fib (k + 1) ∧
      Nat.gcd (2 * Nat.fib (k - 1)) (2 * Nat.fib k) = 2 ∧
      Nat.gcd (2 * Nat.fib k) (2 * Nat.fib (k - 1)) = 2) := by
  rcases Omega.POM.paper_pom_max_fiber_achievers_bsplit_gcd_trichotomy with
    ⟨hConsecutive, hSelf, hBiased, _, _, _⟩
  refine ⟨?_, ?_⟩
  · intro k _hk
    exact hConsecutive k
  · intro k hk
    have hBiasedLR : Nat.gcd (2 * Nat.fib (k - 1)) (2 * Nat.fib k) = 2 :=
      hBiased k (by omega)
    have hBiasedRL : Nat.gcd (2 * Nat.fib k) (2 * Nat.fib (k - 1)) = 2 := by
      rw [Nat.gcd_comm]
      exact hBiasedLR
    exact ⟨hSelf k, hBiasedLR, hBiasedRL⟩

end Omega.Conclusion
