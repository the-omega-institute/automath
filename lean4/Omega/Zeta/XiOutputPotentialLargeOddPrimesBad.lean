import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-output-potential-large-odd-primes-bad`. -/
theorem paper_xi_output_potential_large_odd_primes_bad
    (OddPrime Bad : ℕ → Prop)
    (theta thetaOne : ℕ → ℝ)
    (hEventually : ∃ p0, ∀ p, p0 ≤ p → OddPrime p → (1 / 2 : ℝ) < thetaOne p)
    (hle : ∀ p, OddPrime p → thetaOne p ≤ theta p)
    (hbad : ∀ p, OddPrime p → (1 / 2 : ℝ) < theta p → Bad p) :
    ∃ p0, ∀ p, p0 ≤ p → OddPrime p → Bad p := by
  rcases hEventually with ⟨p0, hp0⟩
  refine ⟨p0, ?_⟩
  intro p hp_ge hp_odd
  exact hbad p hp_odd (lt_of_lt_of_le (hp0 p hp_ge hp_odd) (hle p hp_odd))

end Omega.Zeta
