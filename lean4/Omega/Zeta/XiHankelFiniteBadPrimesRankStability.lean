import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-hankel-finite-bad-primes-rank-stability`. -/
theorem paper_xi_hankel_finite_bad_primes_rank_stability (Delta : ℤ) (hDelta : Delta ≠ 0) :
    {p : ℕ | Nat.Prime p ∧ (p : ℤ) ∣ Delta}.Finite := by
  classical
  refine Set.Finite.subset (s := ((Delta.natAbs.primeFactors : Finset ℕ) : Set ℕ)) ?_ ?_
  · exact Finset.finite_toSet _
  · intro p hp
    rcases hp with ⟨hprime, hdiv⟩
    rw [Finset.mem_coe, Nat.mem_primeFactors_of_ne_zero]
    · exact ⟨hprime, by simpa using (Int.natAbs_dvd_natAbs.mpr hdiv)⟩
    · exact Int.natAbs_ne_zero.mpr hDelta

end Omega.Zeta
