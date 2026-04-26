import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

namespace Omega.Folding

/-- The prime support visible in the fundamental group of one finite-dimensional connected Lie
candidate for `Aut₀`. -/
def foldbinAut0LieLimitPrimeSupport (T : Finset ℕ) : Set ℕ :=
  {p | Nat.Prime p ∧ p ∈ T}

/-- The universal foldbin prime support predicted by the all-primes obstruction. -/
def foldbinAut0UniversalPrimeSupport : Set ℕ :=
  {p | Nat.Prime p}

/-- Paper label: `thm:foldbin-groupoid-aut0-no-universal-lie-limit`.

A connected Lie group can only contribute torsion at finitely many primes, whereas the universal
foldbin support contains every prime. Therefore no finite-prime Lie limit can realize the universal
support. -/
theorem paper_foldbin_groupoid_aut0_no_universal_lie_limit :
    ¬ ∃ T : Finset ℕ,
      foldbinAut0LieLimitPrimeSupport T = foldbinAut0UniversalPrimeSupport := by
  intro h
  rcases h with ⟨T, hT⟩
  rcases Nat.exists_infinite_primes (T.sup id + 1) with ⟨p, hpgt, hpPrime⟩
  have hp_univ : p ∈ foldbinAut0UniversalPrimeSupport := by
    simp [foldbinAut0UniversalPrimeSupport, hpPrime]
  have hp_limit : p ∈ foldbinAut0LieLimitPrimeSupport T := by
    simpa [hT] using hp_univ
  have hp_mem : p ∈ T := hp_limit.2
  have hp_le : p ≤ T.sup id := by
    simpa using (Finset.le_sup hp_mem : id p ≤ T.sup id)
  omega

end Omega.Folding
