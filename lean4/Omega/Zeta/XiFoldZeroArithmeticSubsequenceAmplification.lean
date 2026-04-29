import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.Folding.FoldZeroDivisorTripleReduction
import Omega.Folding.FoldZeroHalfIndexMultiple6
import Omega.Folding.FoldZeroWindow6DensitySharpExponent

namespace Omega.Zeta

open Omega.Folding

/-- Concrete arithmetic-subsequence package for the fold-zero amplification theorem. The
zero-count reduction is specialized to the rigid window-`6` subsequence `m ≡ 4 [MOD 6]`,
and the remaining collision / KL / max-fiber bounds are read from the already formalized
zero-divisor reduction package after fixing the visible lower bound `F_{(m+2)/2}`. -/
structure XiFoldZeroArithmeticSubsequenceAmplificationData where
  m : ℕ
  reductionData : FoldZeroDivisorTripleReductionData
  hm : (m + 2) % 6 = 0
  reduction_m : reductionData.m = m
  reduction_zeroLower : reductionData.zeroLower = Nat.fib ((m + 2) / 2)
  reduction_totalFibers : reductionData.totalFibers = Nat.fib (m + 2)

namespace XiFoldZeroArithmeticSubsequenceAmplificationData

/-- The rigid half-index Fibonacci coset forces at least `F_{(m+2)/2}` zeros. -/
def zeroCountLowerBound (D : XiFoldZeroArithmeticSubsequenceAmplificationData) : Prop :=
  Nat.fib ((D.m + 2) / 2) ≤ (foldZeroFrequencyUnion D.m).card

/-- Collision upper bound obtained by plugging the rigid zero count into the existing reduction
package. -/
def collisionUpperBound (D : XiFoldZeroArithmeticSubsequenceAmplificationData) : Prop :=
  D.reductionData.col ≤ 1 - (Nat.fib ((D.m + 2) / 2) : ℝ) / Nat.fib (D.m + 2)

/-- KL upper bound obtained from the same rigid zero-count reduction. -/
def klUpperBound (D : XiFoldZeroArithmeticSubsequenceAmplificationData) : Prop :=
  D.reductionData.kl ≤ Real.log ((Nat.fib (D.m + 2) : ℝ) - Nat.fib ((D.m + 2) / 2))

/-- Max-fiber gap bound obtained from the same reduction package. -/
def maxFiberGapUpperBound (D : XiFoldZeroArithmeticSubsequenceAmplificationData) : Prop :=
  D.reductionData.maxFiberExcess ≤
    2 ^ D.m *
      Real.sqrt
        (((Nat.fib (D.m + 2) : ℝ) - 1 - Nat.fib ((D.m + 2) / 2)) / Nat.fib (D.m + 2))

/-- The window-`6` lower and upper Fibonacci subsequences have the exact `log φ` exponent, which
packages the deterministic `Θ(φ^{-m/2})` scale discussed in the paper. -/
def asymptoticScale (_ : XiFoldZeroArithmeticSubsequenceAmplificationData) : Prop :=
  Filter.Tendsto
      (fun n : ℕ => Real.log (Nat.fib (3 * n + 3) : ℝ) / (((3 * n + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds (Real.log Real.goldenRatio)) ∧
    Filter.Tendsto
      (fun n : ℕ => Real.log (Nat.fib (6 * n + 6) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)))
      Filter.atTop (nhds (Real.log Real.goldenRatio))

end XiFoldZeroArithmeticSubsequenceAmplificationData

open XiFoldZeroArithmeticSubsequenceAmplificationData

/-- Paper label: `thm:xi-fold-zero-arithmetic-subsequence-amplification`. -/
theorem paper_xi_fold_zero_arithmetic_subsequence_amplification
    (D : XiFoldZeroArithmeticSubsequenceAmplificationData) :
    D.zeroCountLowerBound ∧ D.collisionUpperBound ∧ D.klUpperBound ∧
      D.maxFiberGapUpperBound ∧ D.asymptoticScale := by
  have hzero : D.zeroCountLowerBound := (paper_fold_zero_half_index_multiple6 D.m D.hm).2
  have hred := paper_fold_zero_divisor_triple_reduction D.reductionData
  have hcollision : D.collisionUpperBound := by
    dsimp [XiFoldZeroArithmeticSubsequenceAmplificationData.collisionUpperBound]
    simpa [D.reduction_zeroLower, D.reduction_totalFibers] using hred.1
  have hkl : D.klUpperBound := by
    dsimp [XiFoldZeroArithmeticSubsequenceAmplificationData.klUpperBound]
    simpa [D.reduction_zeroLower, D.reduction_totalFibers] using hred.2.1
  have hmaxFiber : D.maxFiberGapUpperBound := by
    dsimp [XiFoldZeroArithmeticSubsequenceAmplificationData.maxFiberGapUpperBound]
    simpa [D.reduction_m, D.reduction_zeroLower, D.reduction_totalFibers] using hred.2.2.2
  have hasymptotic : D.asymptoticScale := by
    rcases paper_fold_zero_window6_density_sharp_exponent with ⟨_, _, hsmall, hlarge⟩
    exact ⟨hsmall, hlarge⟩
  exact ⟨hzero, hcollision, hkl, hmaxFiber, hasymptotic⟩

end Omega.Zeta
