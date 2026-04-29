import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-replay-algorithm-prime-determinism`. A two-sided
prime-register codec makes replay certificates deterministic on decoded event lists, and
the canonical prime-register encoding is faithful exactly at the decoded-list level. -/
theorem paper_xi_replay_algorithm_prime_determinism {E R PR : Type*} (EncPR : List E → PR)
    (DecPR : PR → List E) (h_left : ∀ xs, DecPR (EncPR xs) = xs)
    (_h_right : ∀ r, EncPR (DecPR r) = r) (Dec : R → List E) :
    (∀ c, DecPR (EncPR (Dec c)) = Dec c) ∧
      (∀ c c', EncPR (Dec c) = EncPR (Dec c') ↔ Dec c = Dec c') := by
  constructor
  · intro c
    exact h_left (Dec c)
  · intro c c'
    constructor
    · intro hEnc
      have hDec := congrArg DecPR hEnc
      simpa [h_left] using hDec
    · intro hDec
      exact congrArg EncPR hDec

end Omega.Zeta
