import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.EpsilonMachineFibMobius
import Omega.Folding.EpsilonMachineStationaryFibonacciTail

namespace Omega.Folding

/-- One-step `1`-emission law along the `R_n` tail. -/
def epsilonMachineZeroRunAlpha (n : ℕ) : ℚ :=
  (Nat.fib (n + 2) : ℚ) / (2 * Nat.fib (n + 4))

/-- Tail law `P(L ≥ n + 1)` for the zero-run length started from `R₀`. -/
def epsilonMachineZeroRunTail (n : ℕ) : ℚ :=
  (Nat.fib (n + 4) : ℚ) / (3 * 2 ^ n)

/-- Point mass `P(L = n + 1)` obtained from the hazard/tail product. -/
def epsilonMachineZeroRunPMF (n : ℕ) : ℚ :=
  epsilonMachineZeroRunAlpha n * epsilonMachineZeroRunTail n

/-- Fibonacci generating-function presentation of the zero-run PGF. -/
def epsilonMachineZeroRunPGFViaFib (z : ℚ) : ℚ :=
  z * (1 + z / 2) / (6 * (1 - z / 2 - z ^ 2 / 4))

/-- Closed-form PGF of the zero-run length. -/
def epsilonMachineZeroRunPGF (z : ℚ) : ℚ :=
  z * (2 + z) / (12 - 6 * z - 3 * z ^ 2)

/-- First derivative of the closed-form PGF. -/
def epsilonMachineZeroRunPGFDeriv (z : ℚ) : ℚ :=
  24 * (1 + z) / (12 - 6 * z - 3 * z ^ 2) ^ 2

/-- Second derivative of the closed-form PGF. -/
def epsilonMachineZeroRunPGFSecondDeriv (z : ℚ) : ℚ :=
  (24 * (12 - 6 * z - 3 * z ^ 2) + 288 * (1 + z) ^ 2) / (12 - 6 * z - 3 * z ^ 2) ^ 3

/-- Mean extracted from the PGF derivative at `z = 1`. -/
def epsilonMachineZeroRunMean : ℚ :=
  epsilonMachineZeroRunPGFDeriv 1

/-- Variance extracted from the first two PGF derivatives at `z = 1`. -/
def epsilonMachineZeroRunVariance : ℚ :=
  epsilonMachineZeroRunPGFSecondDeriv 1 + epsilonMachineZeroRunMean - epsilonMachineZeroRunMean ^ 2

/-- The hazard/tail product simplifies to the closed `F_{n+2}` law. -/
theorem epsilonMachineZeroRunPMF_closed (n : ℕ) :
    epsilonMachineZeroRunPMF n = (Nat.fib (n + 2) : ℚ) / (6 * 2 ^ n) := by
  unfold epsilonMachineZeroRunPMF epsilonMachineZeroRunAlpha epsilonMachineZeroRunTail
  have hfib : (Nat.fib (n + 4) : ℚ) ≠ 0 := by
    have hpos : 0 < (Nat.fib (n + 4) : ℚ) := by
      exact_mod_cast (Nat.fib_pos.mpr (by omega) : 0 < Nat.fib (n + 4))
    exact ne_of_gt hpos
  field_simp [hfib]
  ring

/-- The Fibonacci tail obeys the one-step telescoping product law. -/
theorem epsilonMachineZeroRunTail_step (n : ℕ) :
    epsilonMachineZeroRunTail (n + 1) =
      epsilonMachineZeroRunTail n * (1 - epsilonMachineZeroRunAlpha n) := by
  unfold epsilonMachineZeroRunTail epsilonMachineZeroRunAlpha
  have hfib : (Nat.fib (n + 4) : ℚ) ≠ 0 := by
    have hpos : 0 < (Nat.fib (n + 4) : ℚ) := by
      exact_mod_cast (Nat.fib_pos.mpr (by omega) : 0 < Nat.fib (n + 4))
    exact ne_of_gt hpos
  have hfib₁ : (Nat.fib (n + 5) : ℚ) = 2 * Nat.fib (n + 4) - Nat.fib (n + 2) := by
    norm_num [Nat.fib_add_two]
    ring
  field_simp [hfib]
  rw [hfib₁]
  ring

/-- The Fibonacci generating-function form simplifies to the rational PGF. -/
theorem epsilonMachineZeroRunPGF_closed (z : ℚ) :
    epsilonMachineZeroRunPGFViaFib z = epsilonMachineZeroRunPGF z := by
  unfold epsilonMachineZeroRunPGFViaFib epsilonMachineZeroRunPGF
  have hnum : z * (1 + z / 2) = z * (2 + z) / 2 := by ring
  have hden : 6 * (1 - z / 2 - z ^ 2 / 4) = (12 - 6 * z - 3 * z ^ 2) / 2 := by ring
  rw [hnum, hden]
  by_cases h : 12 - 6 * z - 3 * z ^ 2 = 0
  · simp [h]
  · field_simp [h]

/-- After a zero block of length `n`, the next-`1` conditional law is the shifted Fibonacci ratio
from the local epsilon-machine recursion. This is the chapter-local closed form used in the paper's
zero-run analysis. -/
theorem paper_fold_gauge_anomaly_zero_run_fibonacci (n : ℕ) :
    epsilonMachineZeroRunAlpha (n + 1) = (Nat.fib (n + 3) : ℚ) / (2 * Nat.fib (n + 5)) := by
  simp [epsilonMachineZeroRunAlpha, Nat.add_assoc]

/-- Exact zero-run length package from the Fibonacci/Mobius epsilon-machine seeds.
    cor:fold-gauge-anomaly-epsilon-machine-zero-run-length -/
theorem paper_fold_gauge_anomaly_epsilon_machine_zero_run_length :
    (∀ n : ℕ, epsilonMachineZeroRunPMF n = (Nat.fib (n + 2) : ℚ) / (6 * 2 ^ n)) ∧
    (∀ n : ℕ, epsilonMachineZeroRunTail n = (Nat.fib (n + 4) : ℚ) / (3 * 2 ^ n)) ∧
    (∀ n : ℕ,
      epsilonMachineZeroRunTail (n + 1) =
        epsilonMachineZeroRunTail n * (1 - epsilonMachineZeroRunAlpha n)) ∧
    (∀ z : ℚ, epsilonMachineZeroRunPGFViaFib z = epsilonMachineZeroRunPGF z) ∧
    epsilonMachineZeroRunMean = 16 / 3 ∧
    epsilonMachineZeroRunVariance = 200 / 9 := by
  have _ := paper_fold_gauge_anomaly_zero_run_fibonacci_seeds
  have _ := paper_fold_epsilon_machine_stationary_fibonacci_tail_seeds
  refine ⟨epsilonMachineZeroRunPMF_closed, fun n => rfl, epsilonMachineZeroRunTail_step,
    epsilonMachineZeroRunPGF_closed, ?_, ?_⟩
  · norm_num [epsilonMachineZeroRunMean, epsilonMachineZeroRunPGFDeriv]
  · norm_num [epsilonMachineZeroRunVariance, epsilonMachineZeroRunMean,
      epsilonMachineZeroRunPGFDeriv, epsilonMachineZeroRunPGFSecondDeriv]

end Omega.Folding
