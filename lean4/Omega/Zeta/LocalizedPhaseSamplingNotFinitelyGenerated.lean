import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-localized-phase-sampling-not-finitely-generated`.
A nontrivial localized prime indicator cannot be a constant finite-generation slope. -/
theorem paper_xi_localized_phase_sampling_not_finitely_generated (S : Finset ℕ)
    (hInside : ∃ p, Nat.Prime p ∧ p ∈ S) (hOutside : ∃ q, Nat.Prime q ∧ q ∉ S) :
    ¬ ∃ r : ℕ, ∀ p, Nat.Prime p → (if p ∈ S then 0 else 1) = r := by
  rintro ⟨r, hr⟩
  rcases hInside with ⟨p, hp_prime, hp_mem⟩
  rcases hOutside with ⟨q, hq_prime, hq_not_mem⟩
  have hr_zero : r = 0 := by
    have hp_eval := hr p hp_prime
    simpa [hp_mem] using hp_eval.symm
  have hr_one : r = 1 := by
    have hq_eval := hr q hq_prime
    simpa [hq_not_mem] using hq_eval.symm
  omega

end Omega.Zeta
