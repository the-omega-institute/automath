import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Folding.Fold

namespace Omega.Folding

/-- Binary length bound for the Fibonacci-weighted value of a resolution-`m` fold input. -/
def foldEncodedValueBitLength (m : ℕ) : ℕ :=
  Nat.log 2 (Nat.fib (m + 3)) + 1

/-- Resolution-cost of the weighted summation phase `N(ω) = ∑ ω_k F_{k+1}`. -/
def foldWeightedSummationResolutionCost (m : ℕ) : ℕ :=
  m

/-- Resolution-cost of greedy Zeckendorf normalization up to the top index `m + 2`. -/
def foldZeckendorfNormalizationResolutionCost (m : ℕ) : ℕ :=
  m + 2

/-- Total resolution-cost of the two-phase normalization algorithm for `Omega.Fold`. -/
def foldResolutionCost (m : ℕ) : ℕ :=
  foldWeightedSummationResolutionCost m + foldZeckendorfNormalizationResolutionCost m

/-- Bit-cost of the weighted summation phase when each intermediate integer has
`foldEncodedValueBitLength m` bits. -/
def foldWeightedSummationBitCost (m : ℕ) : ℕ :=
  m * foldEncodedValueBitLength m

/-- Bit-cost of the greedy Zeckendorf normalization phase. -/
def foldZeckendorfNormalizationBitCost (m : ℕ) : ℕ :=
  (m + 2) * foldEncodedValueBitLength m

/-- Total bit-cost of the two-phase normalization algorithm. -/
def foldBitCost (m : ℕ) : ℕ :=
  foldWeightedSummationBitCost m + foldZeckendorfNormalizationBitCost m

/-- Paper-facing wrapper for the Fibonacci weight-sum identity together with the
logarithmic bitlength bound used in the normalization-complexity estimate. -/
def bitlengthFibStatement (m : ℕ) : Prop :=
  (∑ k ∈ Finset.range m, Nat.fib (k + 2) = Nat.fib (m + 3) - 2) ∧
    Nat.log 2 (Nat.fib (m + 3)) ≤ m + 2

/-- Computing the weighted value and then greedily normalizing it gives the paper's
linear-in-resolution and quadratic-in-bit-complexity bounds for `Omega.Fold`.
    prop:fold-complexity -/
theorem paper_fold_complexity :
    ∀ m : ℕ,
      Nat.log 2 (Nat.fib (m + 3)) ≤ m + 2 ∧
      foldWeightedSummationResolutionCost m ≤ m ∧
      foldZeckendorfNormalizationResolutionCost m ≤ m + 2 ∧
      foldResolutionCost m ≤ 2 * m + 2 ∧
      foldWeightedSummationBitCost m ≤ m * (m + 3) ∧
      foldZeckendorfNormalizationBitCost m ≤ (m + 2) * (m + 3) ∧
      foldBitCost m ≤ 2 * (m + 2) * (m + 3) := by
  intro m
  have hFibBound : Nat.fib (m + 3) ≤ 2 ^ (m + 2) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Omega.fib_le_pow_two (m + 1)
  have hLogBound : Nat.log 2 (Nat.fib (m + 3)) ≤ m + 2 := by
    calc
      Nat.log 2 (Nat.fib (m + 3)) ≤ Nat.log 2 (2 ^ (m + 2)) := Nat.log_mono_right hFibBound
      _ = m + 2 := Nat.log_pow (by norm_num) (m + 2)
  have hBitLength : foldEncodedValueBitLength m ≤ m + 3 := by
    unfold foldEncodedValueBitLength
    omega
  have hWeightedBit : foldWeightedSummationBitCost m ≤ m * (m + 3) := by
    unfold foldWeightedSummationBitCost
    exact Nat.mul_le_mul_left m hBitLength
  have hNormalizeBit : foldZeckendorfNormalizationBitCost m ≤ (m + 2) * (m + 3) := by
    unfold foldZeckendorfNormalizationBitCost
    exact Nat.mul_le_mul_left (m + 2) hBitLength
  refine ⟨hLogBound, ?_, ?_, ?_, hWeightedBit, hNormalizeBit, ?_⟩
  · unfold foldWeightedSummationResolutionCost
    omega
  · unfold foldZeckendorfNormalizationResolutionCost
    omega
  · unfold foldResolutionCost foldWeightedSummationResolutionCost foldZeckendorfNormalizationResolutionCost
    omega
  · unfold foldBitCost
    calc
      foldWeightedSummationBitCost m + foldZeckendorfNormalizationBitCost m
          ≤ m * (m + 3) + (m + 2) * (m + 3) := Nat.add_le_add hWeightedBit hNormalizeBit
      _ = (2 * m + 2) * (m + 3) := by ring
      _ ≤ (2 * (m + 2)) * (m + 3) := by
            exact Nat.mul_le_mul_right (m + 3) (by omega)
      _ = 2 * (m + 2) * (m + 3) := by ring

/-- Fibonacci weights up to resolution `m` sum to the advertised top-order weight, and the
resulting encoded value has logarithmic binary length in `m`.
    lem:bitlength-fib -/
theorem paper_bitlength_fib (m : ℕ) : bitlengthFibStatement m := by
  refine ⟨Omega.fib_weight_sum_range m, ?_⟩
  exact (paper_fold_complexity m).1

end Omega.Folding
