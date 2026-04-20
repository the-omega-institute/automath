import Mathlib.Data.List.Infix
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.EpsilonMachineZeroRunLength
import Omega.Folding.FibonacciPolynomial

namespace Omega.Folding

/-- The Möbius update governing the synchronized two-state tail dynamics. -/
def epsilonMachineMobiusUpdate (p : ℚ) : ℚ :=
  (4 - 2 * p) / (4 - p)

/-- The posterior weight of state `a` after observing the history `10^n`. The base case `n = 2`
is the explicit `100` computation, and longer zero blocks iterate the same Möbius update. -/
def epsilonMachineTenZeroStateA : Nat → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 4 / 5
  | n + 3 => epsilonMachineMobiusUpdate (epsilonMachineTenZeroStateA (n + 2))

/-- The next-symbol `1` law after the history `10^n`. -/
def epsilonMachineTenZeroConditional (n : ℕ) : ℚ :=
  epsilonMachineTenZeroStateA n / 4

/-- The next-symbol `1` law after the history `0^n`, reindexed from the zero-run epsilon-machine
tail law already available in the project. -/
def epsilonMachineAllZeroConditional (n : ℕ) : ℚ :=
  epsilonMachineZeroRunAlpha (n + 1)

/-- Difference between the two histories that share a long terminal zero block. -/
def epsilonMachineStrictlySoficGap (n : ℕ) : ℚ :=
  epsilonMachineTenZeroConditional n - epsilonMachineAllZeroConditional n

/-- The all-zero history of length `n`. -/
def zeroHistory (n : ℕ) : List Bool :=
  List.replicate n false

/-- The history `10^n`. -/
def oneZeroHistory (n : ℕ) : List Bool :=
  true :: List.replicate n false

/-- A concrete shared-suffix witness: both histories end with the same `k`-block of zeros. -/
def historiesShareZeroSuffix (k n : ℕ) : Prop :=
  List.replicate k false <:+ zeroHistory n ∧ List.replicate k false <:+ oneZeroHistory n

/-- The shared suffix together with a mismatch of the next-symbol laws gives a finite-order
Markov obstruction at suffix length `k`. -/
def strictlySoficSuffixWitness (k n : ℕ) : Prop :=
  historiesShareZeroSuffix k n ∧
    epsilonMachineTenZeroConditional n ≠ epsilonMachineAllZeroConditional n

/-- Concrete paper-facing package for the strictly sofic infinite-memory gap. -/
def FoldGaugeAnomalyStrictlySoficInfiniteMemory (n : Nat) : Prop :=
  epsilonMachineTenZeroConditional n = (Nat.fib (n + 1) : ℚ) / (2 * Nat.fib (n + 3)) ∧
    epsilonMachineStrictlySoficGap n =
      (((-1 : ℤ) ^ n : ℚ) / (2 * Nat.fib (n + 3) * Nat.fib (n + 5))) ∧
    epsilonMachineStrictlySoficGap n ≠ 0 ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n → strictlySoficSuffixWitness k n

private theorem replicate_suffix_replicate {α : Type*} (a : α) {k n : ℕ} (hk : k ≤ n) :
    List.replicate k a <:+ List.replicate n a := by
  refine ⟨List.replicate (n - k) a, ?_⟩
  have hnk : n = (n - k) + k := by omega
  have hdrop : n - k + k - k = n - k := by omega
  rw [hnk, List.replicate_add]
  simp [hdrop]

private theorem historiesShareZeroSuffix_of_le (k n : ℕ) (hk : k ≤ n) :
    historiesShareZeroSuffix k n := by
  constructor
  · exact replicate_suffix_replicate false hk
  · refine ⟨true :: List.replicate (n - k) false, ?_⟩
    have hnk : n = (n - k) + k := by omega
    have hdrop : n - k + k - k = n - k := by omega
    rw [oneZeroHistory, hnk, List.replicate_add]
    simp [hdrop]

private theorem epsilonMachineTenZeroStateA_closed_aux (m : ℕ) :
    epsilonMachineTenZeroStateA (m + 2) = (2 * Nat.fib (m + 3) : ℚ) / Nat.fib (m + 5) := by
  induction m with
  | zero =>
      norm_num [epsilonMachineTenZeroStateA]
  | succ m ih =>
      have hF5 : (Nat.fib (m + 5) : ℚ) ≠ 0 := by
        exact ne_of_gt <| by
          exact_mod_cast (Nat.fib_pos.mpr (by omega) : 0 < Nat.fib (m + 5))
      have hFib5 : (Nat.fib (m + 5) : ℚ) = Nat.fib (m + 3) + Nat.fib (m + 4) := by
        exact_mod_cast (Nat.fib_add_two (n := m + 3))
      have hFib6 : (Nat.fib (m + 6) : ℚ) = Nat.fib (m + 4) + Nat.fib (m + 5) := by
        exact_mod_cast (Nat.fib_add_two (n := m + 4))
      have hSub : (Nat.fib (m + 5) : ℚ) - Nat.fib (m + 3) = Nat.fib (m + 4) := by
        linarith
      have hComb : 2 * (Nat.fib (m + 5) : ℚ) - Nat.fib (m + 3) = Nat.fib (m + 6) := by
        linarith
      have hCombNe : (2 * (Nat.fib (m + 5) : ℚ) - Nat.fib (m + 3)) ≠ 0 := by
        rw [hComb]
        exact ne_of_gt <| by
          exact_mod_cast (Nat.fib_pos.mpr (by omega) : 0 < Nat.fib (m + 6))
      let a : ℚ := Nat.fib (m + 3)
      let b : ℚ := Nat.fib (m + 5)
      have hb_ne : b ≠ 0 := hF5
      have hEqNum : 4 - 2 * (2 * a / b) = 4 * (b - a) / b := by
        field_simp [a, b, hb_ne]
        ring
      have hEqDen : 4 - 2 * a / b = 2 * (2 * b - a) / b := by
        field_simp [a, b, hb_ne]
        ring
      have hQuot :
          (4 * (b - a) / b) / (2 * (2 * b - a) / b) = (2 * (b - a)) / (2 * b - a) := by
        field_simp [a, b, hb_ne, hCombNe]
        ring
      calc
        epsilonMachineTenZeroStateA (m + 3)
            = epsilonMachineMobiusUpdate (epsilonMachineTenZeroStateA (m + 2)) := by
                simp [epsilonMachineTenZeroStateA]
        _ = epsilonMachineMobiusUpdate ((2 * Nat.fib (m + 3) : ℚ) / Nat.fib (m + 5)) := by
              rw [ih]
        _ = (2 * ((Nat.fib (m + 5) : ℚ) - Nat.fib (m + 3))) /
              (2 * (Nat.fib (m + 5) : ℚ) - Nat.fib (m + 3)) := by
              unfold epsilonMachineMobiusUpdate
              rw [hEqNum, hEqDen, hQuot]
        _ = (2 * Nat.fib (m + 4) : ℚ) / Nat.fib (m + 6) := by rw [hSub, hComb]

private theorem epsilonMachineTenZeroStateA_closed (n : ℕ) (hn : 2 ≤ n) :
    epsilonMachineTenZeroStateA n = (2 * Nat.fib (n + 1) : ℚ) / Nat.fib (n + 3) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    epsilonMachineTenZeroStateA_closed_aux m

private theorem epsilonMachineTenZeroConditional_closed (n : ℕ) (hn : 2 ≤ n) :
    epsilonMachineTenZeroConditional n = (Nat.fib (n + 1) : ℚ) / (2 * Nat.fib (n + 3)) := by
  rw [epsilonMachineTenZeroConditional, epsilonMachineTenZeroStateA_closed n hn]
  field_simp
  ring

private theorem epsilonMachineAllZeroConditional_closed (n : ℕ) :
    epsilonMachineAllZeroConditional n = (Nat.fib (n + 3) : ℚ) / (2 * Nat.fib (n + 5)) := by
  rfl

private theorem fib_shifted_cassini (n : ℕ) :
    ((Nat.fib (n + 1) : ℤ) * Nat.fib (n + 5) - Nat.fib (n + 3) ^ 2) = (-1) ^ n := by
  have hCassiniBase : (Nat.fib (n + 1) : ℤ) * Nat.fib (n + 3) - Nat.fib (n + 2) ^ 2 = (-1) ^ n := by
    have hCassini := fib_product_cassini (n + 1)
    have hCassini' : (Nat.fib (n + 1) : ℤ) * Nat.fib (n + 3) =
        (Nat.fib (n + 2) : ℤ) ^ 2 + (-1) ^ n := by
      simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hCassini
    linarith
  have hFib3 : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
    exact_mod_cast (Nat.fib_add_two (n := n + 1))
  have hFib5Nat : Nat.fib (n + 5) = Nat.fib (n + 1) * Nat.fib 3 + Nat.fib (n + 2) * Nat.fib 4 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.fib_add (n + 1) 3
  have hFib5 : (Nat.fib (n + 5) : ℤ) = 2 * Nat.fib (n + 1) + 3 * Nat.fib (n + 2) := by
    have hFib5' :
        (Nat.fib (n + 5) : ℤ) = Nat.fib (n + 1) * Nat.fib 3 + Nat.fib (n + 2) * Nat.fib 4 := by
      exact_mod_cast hFib5Nat
    rw [hFib5']
    norm_num
    ring
  nlinarith

private theorem epsilonMachineStrictlySoficGap_closed (n : ℕ) (hn : 2 ≤ n) :
    epsilonMachineStrictlySoficGap n =
      (((-1 : ℤ) ^ n : ℚ) / (2 * Nat.fib (n + 3) * Nat.fib (n + 5))) := by
  have hF3 : (Nat.fib (n + 3) : ℚ) ≠ 0 := by
    exact ne_of_gt <| by
      exact_mod_cast (Nat.fib_pos.mpr (by omega) : 0 < Nat.fib (n + 3))
  have hF5 : (Nat.fib (n + 5) : ℚ) ≠ 0 := by
    exact ne_of_gt <| by
      exact_mod_cast (Nat.fib_pos.mpr (by omega) : 0 < Nat.fib (n + 5))
  have hCassiniQ :
      ((Nat.fib (n + 1) : ℚ) * Nat.fib (n + 5) - (Nat.fib (n + 3) : ℚ) ^ 2) =
        ((-1 : ℤ) ^ n : ℚ) := by
    exact_mod_cast fib_shifted_cassini n
  calc
    epsilonMachineStrictlySoficGap n
        = (((Nat.fib (n + 1) : ℚ) * Nat.fib (n + 5) - (Nat.fib (n + 3) : ℚ) ^ 2) /
            (2 * Nat.fib (n + 3) * Nat.fib (n + 5))) := by
            rw [epsilonMachineStrictlySoficGap, epsilonMachineTenZeroConditional_closed n hn,
              epsilonMachineAllZeroConditional_closed]
            field_simp [hF3, hF5]
    _ = (((-1 : ℤ) ^ n : ℚ) / (2 * Nat.fib (n + 3) * Nat.fib (n + 5))) := by
          rw [hCassiniQ]

private theorem epsilonMachineStrictlySoficGap_nonzero (n : ℕ) (hn : 2 ≤ n) :
    epsilonMachineStrictlySoficGap n ≠ 0 := by
  rw [epsilonMachineStrictlySoficGap_closed n hn]
  have hnum : (((-1 : ℤ) ^ n : ℚ)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero n (by norm_num : (-1 : ℤ) ≠ 0))
  have hden : (2 * Nat.fib (n + 3) * Nat.fib (n + 5) : ℚ) ≠ 0 := by
    have hF3 : (Nat.fib (n + 3) : ℚ) ≠ 0 := by
      exact ne_of_gt <| by
        exact_mod_cast (Nat.fib_pos.mpr (by omega) : 0 < Nat.fib (n + 3))
    have hF5 : (Nat.fib (n + 5) : ℚ) ≠ 0 := by
      exact ne_of_gt <| by
        exact_mod_cast (Nat.fib_pos.mpr (by omega) : 0 < Nat.fib (n + 5))
    exact mul_ne_zero (mul_ne_zero (by norm_num) hF3) hF5
  exact div_ne_zero hnum hden

private theorem epsilonMachineStrictlySoficConditional_ne (n : ℕ) (hn : 2 ≤ n) :
    epsilonMachineTenZeroConditional n ≠ epsilonMachineAllZeroConditional n := by
  intro hEq
  apply epsilonMachineStrictlySoficGap_nonzero n hn
  simp [epsilonMachineStrictlySoficGap, hEq]

/-- The `10^n` law differs from the `0^n` law by a Cassini gap, so arbitrarily long shared zero
suffixes still fail to determine the next-symbol law. This is the explicit strictly sofic,
infinite-memory obstruction from the paper.
    thm:fold-gauge-anomaly-strictly-sofic-infinite-memory -/
theorem paper_fold_gauge_anomaly_strictly_sofic_infinite_memory (n : Nat) (hn : 2 <= n) :
    FoldGaugeAnomalyStrictlySoficInfiniteMemory n := by
  refine ⟨epsilonMachineTenZeroConditional_closed n hn, epsilonMachineStrictlySoficGap_closed n hn,
    epsilonMachineStrictlySoficGap_nonzero n hn, ?_⟩
  intro k hk1 hk2
  refine ⟨historiesShareZeroSuffix_of_le k n hk2, ?_⟩
  exact epsilonMachineStrictlySoficConditional_ne n hn

end Omega.Folding
