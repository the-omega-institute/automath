import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Omega.CircleDimension.AnomalyFunctorialSplittingObstructionRge2Tor

namespace Omega.CircleDimension

/-- Prime-support wrapper for the anomaly splitting obstruction. -/
structure CdimAnomalySplittingPrimeSupportData where
  freeRank : ℕ
  freeRank_ge_two : 2 ≤ freeRank
  torsionOrder : ℕ
  torsionPositive : 1 ≤ torsionOrder
  primeSupport : Finset ℕ
  prime_mem_iff : ∀ p : ℕ, p ∈ primeSupport ↔ Nat.Prime p ∧ p ∣ torsionOrder

namespace CdimAnomalySplittingPrimeSupportData

/-- The chapter-local obstruction package attached to the same rank and torsion order. -/
def toBaseData (D : CdimAnomalySplittingPrimeSupportData) :
    CdimAnomalyFunctorialSplittingObstructionData where
  freeRank := D.freeRank
  torsionOrder := D.torsionOrder
  torsionPositive := D.torsionPositive

/-- Existence of a supported torsion prime. -/
def HasSupportedPrime (D : CdimAnomalySplittingPrimeSupportData) : Prop :=
  ∃ p ∈ D.primeSupport, Nat.Prime p

/-- Concrete corollary package: the obstruction is equivalent to the existence of a supported
torsion prime, and each supported prime rules out a fixed point for the chapter-local twist
translation. -/
def Holds (D : CdimAnomalySplittingPrimeSupportData) : Prop :=
  let B := D.toBaseData
  (¬ B.naturalSplitting ↔ D.HasSupportedPrime) ∧
    ∀ p, p ∈ D.primeSupport → ¬ ∃ x : ZMod D.torsionOrder, B.twistTranslation x = x

private lemma hasSupportedPrime_iff_torsion_nontrivial (D : CdimAnomalySplittingPrimeSupportData) :
    D.HasSupportedPrime ↔ D.torsionOrder ≠ 1 := by
  constructor
  · rintro ⟨p, hp, hpprime⟩ htriv
    have hpdvd : p ∣ 1 := by
      simpa [htriv] using (D.prime_mem_iff p).1 hp |>.2
    exact hpprime.not_dvd_one hpdvd
  · intro htor
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd htor
    exact ⟨p, (D.prime_mem_iff p).2 ⟨hpprime, hpdvd⟩, hpprime⟩

end CdimAnomalySplittingPrimeSupportData

open CdimAnomalySplittingPrimeSupportData

/-- Paper label: `cor:cdim-anomaly-splitting-prime-support`. For rank at least `2`, the
functorial splitting obstruction is exactly the existence of a supported torsion prime, and each
such prime reuses the chapter-local twist-translation obstruction to rule out a natural section. -/
theorem paper_cdim_anomaly_splitting_prime_support (D : CdimAnomalySplittingPrimeSupportData) :
    D.Holds := by
  let B := D.toBaseData
  have hbase := paper_cdim_anomaly_functorial_splitting_obstruction_rge2_tor B
  have hrank : ¬ B.rankLeOne := by
    intro hle
    have hle' : D.freeRank ≤ 1 := by
      simpa [B, CdimAnomalyFunctorialSplittingObstructionData.rankLeOne] using hle
    exact Nat.not_succ_le_self 1 (le_trans D.freeRank_ge_two hle')
  have hiff : ¬ B.naturalSplitting ↔ D.HasSupportedPrime := by
    constructor
    · intro hsplit
      have hnotTor : ¬ B.torsionTrivial := by
        intro htor
        exact hsplit (hbase.mpr (Or.inr htor))
      simpa [B, CdimAnomalyFunctorialSplittingObstructionData.torsionTrivial] using
        (hasSupportedPrime_iff_torsion_nontrivial D).2 hnotTor
    · intro hprime hsplit
      rcases hbase.mp hsplit with hle | htor
      · exact hrank hle
      · have hnotTor : D.torsionOrder ≠ 1 :=
          (hasSupportedPrime_iff_torsion_nontrivial D).1 hprime
        exact hnotTor htor
  refine ⟨?_, ?_⟩
  · exact hiff
  · intro p hp hfix
    have hprime : D.HasSupportedPrime := ⟨p, hp, (D.prime_mem_iff p).1 hp |>.1⟩
    have hno : ¬ B.naturalSplitting := hiff.mpr hprime
    exact hno (Or.inr (Or.inr hfix))

end Omega.CircleDimension
