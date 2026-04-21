import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete finite prime-channel data for the boundary-cycle-rank/Loewner comparison package. -/
structure BoundaryCycleRankLoewnerPrimeLowerBoundData where
  Channel : Type
  instFintypeChannel : Fintype Channel
  rank : ℕ
  rankPos : 1 ≤ rank
  encodeRank : Fin rank → Channel
  encodeRankInjective : Function.Injective encodeRank
  channelCountPos : 1 ≤ Fintype.card Channel
  primeSeq : Fin (Fintype.card Channel) → ℕ
  primeSeqStrictMono : StrictMono primeSeq
  primeSeqPrime : ∀ i, Nat.Prime (primeSeq i)

attribute [instance] BoundaryCycleRankLoewnerPrimeLowerBoundData.instFintypeChannel

namespace BoundaryCycleRankLoewnerPrimeLowerBoundData

/-- The finite prime-channel count `k`. -/
def channelCount (D : BoundaryCycleRankLoewnerPrimeLowerBoundData) : ℕ :=
  Fintype.card D.Channel

/-- The first prime-channel index. -/
def firstChannel (D : BoundaryCycleRankLoewnerPrimeLowerBoundData) : Fin D.channelCount :=
  ⟨0, lt_of_lt_of_le (by decide : 0 < 1) D.channelCountPos⟩

/-- The last prime-channel index. -/
def lastChannel (D : BoundaryCycleRankLoewnerPrimeLowerBoundData) : Fin D.channelCount :=
  ⟨D.channelCount - 1, Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 1) D.channelCountPos)
    (by decide : 0 < 1)⟩

/-- The Loewner weight modeled by the double logarithm of a prime-channel modulus. -/
def loewnerWeight (p : ℕ) : ℝ :=
  Real.log (Real.log (p : ℝ))

/-- The rank cannot exceed the number of available finite prime channels. -/
def rankBound (D : BoundaryCycleRankLoewnerPrimeLowerBoundData) : Prop :=
  D.rank ≤ D.channelCount

/-- The first Loewner weight is bounded above by the last one along the strictly increasing prime
sequence. -/
def loewnerPrimeLowerBound (D : BoundaryCycleRankLoewnerPrimeLowerBoundData) : Prop :=
  loewnerWeight (D.primeSeq D.firstChannel) ≤ loewnerWeight (D.primeSeq D.lastChannel)

/-- Under the minimal-budget specialization `k = r`, the same rank/Loewner lower bound specializes
to the exact budget threshold. -/
def minimalBudgetAsymptotic (D : BoundaryCycleRankLoewnerPrimeLowerBoundData) : Prop :=
  D.channelCount = D.rank → D.rankBound ∧ D.loewnerPrimeLowerBound

end BoundaryCycleRankLoewnerPrimeLowerBoundData

/-- Paper label: `cor:conclusion-boundary-cycle-rank-loewner-prime-lower-bound`. -/
theorem paper_conclusion_boundary_cycle_rank_loewner_prime_lower_bound
    (D : BoundaryCycleRankLoewnerPrimeLowerBoundData) :
    BoundaryCycleRankLoewnerPrimeLowerBoundData.rankBound D ∧
      BoundaryCycleRankLoewnerPrimeLowerBoundData.loewnerPrimeLowerBound D ∧
      BoundaryCycleRankLoewnerPrimeLowerBoundData.minimalBudgetAsymptotic D := by
  have hRank :
      BoundaryCycleRankLoewnerPrimeLowerBoundData.rankBound D := by
    simpa [BoundaryCycleRankLoewnerPrimeLowerBoundData.rankBound,
      BoundaryCycleRankLoewnerPrimeLowerBoundData.channelCount, Fintype.card_fin] using
      Fintype.card_le_of_injective D.encodeRank D.encodeRankInjective
  have hFirstPrimeTwo : 2 ≤ D.primeSeq D.firstChannel :=
    (D.primeSeqPrime D.firstChannel).two_le
  have hLastPrimeTwo : 2 ≤ D.primeSeq D.lastChannel :=
    (D.primeSeqPrime D.lastChannel).two_le
  have hFirstPrimePos : (0 : ℝ) < D.primeSeq D.firstChannel := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hFirstPrimeTwo
  have hLastPrimePos : (0 : ℝ) < D.primeSeq D.lastChannel := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hLastPrimeTwo
  have hFirstLogPos : 0 < Real.log (D.primeSeq D.firstChannel : ℝ) := by
    refine Real.log_pos ?_
    exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hFirstPrimeTwo
  have hLastLogPos : 0 < Real.log (D.primeSeq D.lastChannel : ℝ) := by
    refine Real.log_pos ?_
    exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hLastPrimeTwo
  have hIndex :
      D.firstChannel ≤ D.lastChannel := by
    change 0 ≤ BoundaryCycleRankLoewnerPrimeLowerBoundData.channelCount D - 1
    exact Nat.zero_le _
  have hPrimeLe :
      (D.primeSeq D.firstChannel : ℝ) ≤ D.primeSeq D.lastChannel := by
    exact_mod_cast D.primeSeqStrictMono.monotone hIndex
  have hLogLe :
      Real.log (D.primeSeq D.firstChannel : ℝ) ≤ Real.log (D.primeSeq D.lastChannel : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (by simpa [Set.mem_Ioi] using hFirstPrimePos)
      (by simpa [Set.mem_Ioi] using hLastPrimePos) hPrimeLe
  have hLoewner :
      BoundaryCycleRankLoewnerPrimeLowerBoundData.loewnerPrimeLowerBound D := by
    exact Real.strictMonoOn_log.monotoneOn (by simpa [Set.mem_Ioi] using hFirstLogPos)
      (by simpa [Set.mem_Ioi] using hLastLogPos) hLogLe
  refine ⟨hRank, hLoewner, ?_⟩
  intro hMinimal
  exact ⟨by simpa [hMinimal] using hRank, hLoewner⟩

end

end Omega.Conclusion
