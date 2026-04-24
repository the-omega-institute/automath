import Mathlib.Tactic
import Omega.POM.EllipsoidIsoperimetricVariance

namespace Omega.POM

/-- Paper label: `prop:pom-godel-axis-variance-no-gap`.
Choosing the zero exponent vector makes every prime axis equal to `1`, so the logarithmic
axis-length variance vanishes exactly. -/
theorem paper_pom_godel_axis_variance_no_gap (d : ℕ) (_hd : 0 < d) (primes : Fin d → ℕ)
    (_hprime : ∀ i, Nat.Prime (primes i)) (_hinj : Function.Injective primes) :
    ∀ ε > 0, ∃ alpha : Fin d → ℕ,
      Omega.POM.ellipsoidLogVariance d (fun i => ((primes i : ℝ) ^ (alpha i))) ≤ ε := by
  intro ε hε
  refine ⟨fun _ => 0, ?_⟩
  have hvar : Omega.POM.ellipsoidLogVariance d (fun i => ((primes i : ℝ) ^ (0 : ℕ))) = 0 := by
    simp [Omega.POM.ellipsoidLogVariance, Omega.POM.ellipsoidLogMean]
  rw [hvar]
  exact hε.le

end Omega.POM
