import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-replay-godel-prime-terminality`. A prime-register
encoder/decoder pair with two-sided inverse laws gives a unique canonical replay lift, and
the canonical lift is injective exactly when the underlying decoder is injective. -/
theorem paper_xi_replay_godel_prime_terminality {E R PR : Type*} (EncPR : List E → PR)
    (DecPR : PR → List E) (h_left : ∀ xs, DecPR (EncPR xs) = xs)
    (h_right : ∀ r, EncPR (DecPR r) = r) (Dec : R → List E) :
    (∀ Φ : R → PR, (∀ c, DecPR (Φ c) = Dec c) → Φ = fun c => EncPR (Dec c)) ∧
      (Function.Injective (fun c : R => EncPR (Dec c)) ↔ Function.Injective Dec) := by
  constructor
  · intro Φ hΦ
    funext c
    calc
      Φ c = EncPR (DecPR (Φ c)) := (h_right (Φ c)).symm
      _ = EncPR (Dec c) := by rw [hΦ c]
  · constructor
    · intro hEnc c d hDec
      apply hEnc
      exact congrArg EncPR hDec
    · intro hDec c d hEnc
      apply hDec
      have h := congrArg DecPR hEnc
      simpa [h_left] using h

end Omega.Zeta
