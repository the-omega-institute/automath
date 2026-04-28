import Mathlib.Data.Nat.Find

namespace Omega.Zeta

/-- Paper label: `prop:xi-toeplitz-first-failure-minimal-blocking-polynomial`. -/
theorem paper_xi_toeplitz_first_failure_minimal_blocking_polynomial
    (Bad : ℕ → Prop) [DecidablePred Bad] (Witness : ℕ → Type)
    (hwitness : ∀ N, Bad N → Nonempty (Witness N)) (hexists : ∃ N, Bad N) :
    ∃ Nstar, Bad Nstar ∧ (∀ M, M < Nstar → ¬ Bad M) ∧ Nonempty (Witness Nstar) := by
  let Nstar := Nat.find hexists
  have hbad : Bad Nstar := Nat.find_spec hexists
  refine ⟨Nstar, hbad, ?_, hwitness Nstar hbad⟩
  intro M hM hBadM
  exact (Nat.not_lt_of_ge (Nat.find_min' hexists hBadM)) hM

end Omega.Zeta
