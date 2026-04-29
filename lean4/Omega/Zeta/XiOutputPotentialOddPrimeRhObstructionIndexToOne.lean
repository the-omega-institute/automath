import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-output-potential-odd-prime-rh-obstruction-index-to-one`. -/
theorem paper_xi_output_potential_odd_prime_rh_obstruction_index_to_one
    (OddPrime : ℕ → Prop) (theta thetaOne : ℕ → ℝ)
    (hdom : ∃ p0, ∀ p ≥ p0, OddPrime p → (1 / 2 : ℝ) < thetaOne p)
    (hle : ∀ p, OddPrime p → thetaOne p ≤ theta p) :
    ∃ p0, ∀ p ≥ p0, OddPrime p → (1 / 2 : ℝ) < theta p := by
  rcases hdom with ⟨p0, hp0⟩
  refine ⟨p0, ?_⟩
  intro p hp hpOdd
  exact lt_of_lt_of_le (hp0 p hp hpOdd) (hle p hpOdd)

end Omega.Zeta
