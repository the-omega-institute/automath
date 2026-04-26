import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit

namespace Omega.CircleDimension

open Omega.Zeta

/-- Paper label: `cor:cdim-star-finite-prime-register-limit`. A subgroup of `ℚ` whose elements
all have denominator prime support inside one finite set `S` lies in `ℤ[1/S]`; conversely, if
every finite support misses some denominator prime used by an element of the subgroup, then no
finite localization stage contains the subgroup. -/
theorem paper_cdim_star_finite_prime_register_limit (A : AddSubgroup ℚ) :
    ((∃ S : Finset ℕ, ∀ q : ℚ, q ∈ A → Omega.Zeta.denominatorSupportedBy S q) →
        ∃ S : Finset ℕ, A ≤ Omega.Zeta.localizedIntegerSubgroup S) ∧
      ((∀ S : Finset ℕ, ∃ q : ℚ, q ∈ A ∧ ¬ Omega.Zeta.denominatorSupportedBy S q) →
        ∀ S : Finset ℕ, ¬ A ≤ Omega.Zeta.localizedIntegerSubgroup S) := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_⟩
    intro q hq
    exact hS q hq
  · intro hA S hle
    rcases hA S with ⟨q, hqA, hqS⟩
    exact hqS (hle hqA)

end Omega.CircleDimension
