import Omega.Zeta.HankelBadPrimeSelectionProbability
import Omega.Folding.GodelFiniteDictionaryBitlength
import Mathlib.Tactic

namespace Omega.Zeta

open Omega.Folding

theorem paper_xi_hankel_short_prime_avoids_badset (Delta : ℕ) (hDelta : 3 ≤ Delta) :
    ∃ n < Nat.log2 (2 * Delta), Nat.Prime (nthPrime n) ∧ nthPrime n ∉ Delta.primeFactors := by
  classical
  let M := Nat.log2 (2 * Delta)
  have hDelta_pos : 0 < Delta := by omega
  have hM_pos : 0 < M := by
    dsimp [M]
    rw [Nat.log2_eq_log_two]
    exact Nat.log_pos Nat.one_lt_two (by omega)
  have hlog_eq : M = Nat.log2 Delta + 1 := by
    dsimp [M]
    rw [Nat.log2_eq_log_two, show 2 * Delta = Delta * 2 by omega, Nat.log2_eq_log_two]
    exact Nat.log_mul_base Nat.one_lt_two hDelta_pos.ne'
  have hlog_lt : Nat.log2 Delta < M := by
    rw [hlog_eq]
    exact Nat.lt_succ_self _
  have hinjNth : Function.Injective (fun i : Fin M => nthPrime i.1) := by
    intro i j hij
    apply Fin.ext
    simpa [nthPrime] using (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hij
  by_contra h
  push_neg at h
  have hallBad : ∀ n < M, nthPrime n ∈ Delta.primeFactors := by
    intro n hn
    exact h n hn (nthPrime_prime n)
  let sample : Fin M → ℕ := fun i => nthPrime i.1
  have hsample := paper_xi_hankel_badprime_selection_probability hM_pos Delta hDelta_pos.ne' sample
    hinjNth
  have hleft : ((M : ℚ) / (M : ℚ)) ≤ (Delta.primeFactors.card : ℚ) / (M : ℚ) := by
    simpa [sample, sampledBadPrimeCount, failureProbabilityLeBadPrimeRatio, hallBad] using hsample.1
  have hright : (Delta.primeFactors.card : ℚ) / (M : ℚ) ≤ (Nat.log2 Delta : ℚ) / (M : ℚ) := by
    simpa [badPrimeRatioLeBitlengthRatio] using hsample.2
  have hone_le : (1 : ℚ) ≤ (Nat.log2 Delta : ℚ) / (M : ℚ) := by
    have hMq_ne : (M : ℚ) ≠ 0 := by exact_mod_cast hM_pos.ne'
    simpa [hMq_ne] using le_trans hleft hright
  have hratio_lt : (Nat.log2 Delta : ℚ) / (M : ℚ) < 1 := by
    have hMq : (0 : ℚ) < M := by exact_mod_cast hM_pos
    have hnum_lt : (Nat.log2 Delta : ℚ) < M := by exact_mod_cast hlog_lt
    rw [div_lt_one hMq]
    simpa using hnum_lt
  exact (not_le_of_gt hratio_lt) hone_le

end Omega.Zeta
