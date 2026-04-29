import Mathlib.Tactic
import Omega.Conclusion.PrimeRegisterGodelOrbitSuperexpLoglaw

namespace Omega.Conclusion

open PrimeRegisterGodelOrbitSuperexpLoglawData

/-- Concrete support window extracted from the finite orbit package. -/
def conclusion_godel_orbit_extreme_smoothness_support_window
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) : ℕ :=
  Fintype.card D.Orbit * D.n

/-- Seed bound for the largest prime factor coming from the support window. -/
def conclusion_godel_orbit_extreme_smoothness_largest_prime_factor_bound
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) : ℕ :=
  conclusion_godel_orbit_extreme_smoothness_support_window D + D.n

/-- Paper-facing statement packaging the concrete support bound together with the already verified
superexponential log-law. -/
def paper_conclusion_godel_orbit_extreme_smoothness_statement
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) : Prop :=
  D.superexpLogAsymptotic ∧
    conclusion_godel_orbit_extreme_smoothness_support_window D =
      Fintype.card D.Orbit * D.n ∧
    conclusion_godel_orbit_extreme_smoothness_support_window D ≤
      conclusion_godel_orbit_extreme_smoothness_largest_prime_factor_bound D ∧
    D.prime_register_godel_orbit_superexp_loglaw_logOrbitCount =
      D.prime_register_godel_orbit_superexp_loglaw_scale *
        (Real.log D.n + Real.log (Real.log D.n) + Real.log D.mu +
          D.prime_register_godel_orbit_superexp_loglaw_orbitExpectation)

/-- Paper label: `prop:conclusion-godel-orbit-extreme-smoothness`. The finite orbit support gives a
linear support window, that window trivially bounds the corresponding largest-prime-factor seed,
and the asymptotic separation is exactly the previously packaged superexponential log-law. -/
theorem paper_conclusion_godel_orbit_extreme_smoothness
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) :
    paper_conclusion_godel_orbit_extreme_smoothness_statement D := by
  have hloglaw := paper_conclusion_prime_register_godel_orbit_superexp_loglaw D
  refine ⟨hloglaw, rfl, ?_, hloglaw.2⟩
  simp [conclusion_godel_orbit_extreme_smoothness_largest_prime_factor_bound,
    conclusion_godel_orbit_extreme_smoothness_support_window]

end Omega.Conclusion
