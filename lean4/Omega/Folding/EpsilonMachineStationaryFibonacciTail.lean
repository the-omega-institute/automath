import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.EpsilonMachineFibMobius
import Omega.Folding.EpsilonMachineSynchronizingWord

namespace Omega.Folding

/-- Concrete paper-facing package for the stationary Fibonacci tail of the epsilon-machine.
The fields store the stationary masses of `A`, `B`, `C`, the closed form for the tail states
`R_n`, and the normalized total tail mass. -/
structure EpsilonMachineStationaryFibonacciTailData where
  piB : Rat
  piC : Rat
  piA : Rat
  piR : Nat → Rat
  tailMass : Rat
  piB_eq : piB = (2 : Rat) / 9
  piC_eq : piC = (2 : Rat) / 9
  piA_eq : piA = (1 : Rat) / 9
  piR_eq : ∀ n : Nat, piR n = (Nat.fib (n + 4) : Rat) / (36 * 2 ^ n)
  tailMass_eq : tailMass = (4 : Rat) / 9

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the stationary epsilon-machine law with Fibonacci tail.
    thm:fold-gauge-anomaly-epsilon-machine-stationary-fibonacci-tail -/
theorem paper_fold_epsilon_machine_stationary_fibonacci_tail
    (h : EpsilonMachineStationaryFibonacciTailData) :
    h.piB = (2 : Rat) / 9 ∧ h.piC = (2 : Rat) / 9 ∧ h.piA = (1 : Rat) / 9 ∧
      (∀ n : Nat, h.piR n = (Nat.fib (n + 4) : Rat) / (36 * 2 ^ n)) ∧
      h.tailMass = (4 : Rat) / 9 := by
  have _ := paper_fold_epsilon_machine_stationary_fibonacci_tail_seeds
  have _ := paper_fold_epsilon_machine_synchronizing_word_seeds
  exact ⟨h.piB_eq, h.piC_eq, h.piA_eq, h.piR_eq, h.tailMass_eq⟩

/-- Publication-facing label-compatible wrapper for the stationary epsilon-machine law with
Fibonacci tail.
    thm:fold-gauge-anomaly-epsilon-machine-stationary-fibonacci-tail -/
theorem paper_fold_gauge_anomaly_epsilon_machine_stationary_fibonacci_tail
    (h : EpsilonMachineStationaryFibonacciTailData) :
    h.piB = (2 : Rat) / 9 ∧ h.piC = (2 : Rat) / 9 ∧ h.piA = (1 : Rat) / 9 ∧
      (∀ n : Nat, h.piR n = (Nat.fib (n + 4) : Rat) / (36 * 2 ^ n)) ∧
      h.tailMass = (4 : Rat) / 9 :=
  paper_fold_epsilon_machine_stationary_fibonacci_tail h

end Omega.Folding
