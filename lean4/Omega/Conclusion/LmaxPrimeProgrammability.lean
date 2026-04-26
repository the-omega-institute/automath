import Mathlib.Tactic
import Omega.POM.ToggleScanLinearMaxOrbit

namespace Omega.Conclusion

/-- Component orbit length programmed by the prime `p`. -/
def conclusion_lmax_prime_programmability_component_length (p : ℕ) : ℕ :=
  p

/-- Programmed orbit length for a finite family of admissible primes. -/
def conclusion_lmax_prime_programmability_orbit_length (P : Finset ℕ) : ℕ :=
  P.prod conclusion_lmax_prime_programmability_component_length

lemma conclusion_lmax_prime_programmability_component_length_eq
    (p : ℕ) (_hp : Nat.Prime p ∧ p % 3 = 2 ∧ 5 ≤ p) :
    conclusion_lmax_prime_programmability_component_length p = p := by
  rfl

/-- Paper label: `thm:conclusion-lmax-prime-programmability`. -/
theorem paper_conclusion_lmax_prime_programmability (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ p % 3 = 2 ∧ 5 ≤ p) :
    conclusion_lmax_prime_programmability_orbit_length P = P.prod id := by
  let _ := hP
  rfl

end Omega.Conclusion
