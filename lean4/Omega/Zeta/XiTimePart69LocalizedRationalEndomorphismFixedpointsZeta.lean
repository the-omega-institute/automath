import Mathlib.Tactic
import Omega.Zeta.LocalizedSolenoidEndomorphismRing
import Omega.Zeta.XiLocalizedSolenoidPeriodicPointFormula

namespace Omega.Zeta

noncomputable section

/-- Fixed-point count for the chapter-local rational-endomorphism wrapper. In the simplified model
we package the integer scalar case, which already records the localized quotient index appearing in
the periodic-point formula. -/
def xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta_fixedPointCount
    (S : FinitePrimeLocalization) (a n : ℕ) : ℕ :=
  Nat.card (xi_localized_solenoid_periodic_point_formula_fixModel S a n)

/-- The `n`-th Artin--Mazur coefficient attached to the localized scalar endomorphism. -/
def xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta_artinMazurCoefficient
    (S : FinitePrimeLocalization) (a n : ℕ) : ℚ :=
  (xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta_fixedPointCount S a n : ℚ) / n

/-- Chapter-local wrapper: the localized endomorphism ring is the expected scalar model, every
iterate has fixed-point count given by the localized quotient ledger, and the Artin--Mazur series
coefficients are exactly those fixed-point counts divided by the iterate index. -/
def xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta_statement : Prop :=
  ∀ (S : FinitePrimeLocalization) (a : ℕ), 2 ≤ a →
    LocalizedSolenoidEndomorphismRing S ∧
      (∀ n : ℕ, 1 ≤ n →
        xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta_fixedPointCount S a n =
          localizedIndex S (a ^ n - 1)) ∧
      ∀ n : ℕ, 1 ≤ n →
        xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta_artinMazurCoefficient S a n =
          ((localizedIndex S (a ^ n - 1) : ℚ) / n)

/-- Paper label: `thm:xi-time-part69-localized-rational-endomorphism-fixedpoints-zeta`. -/
theorem paper_xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta :
    xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta_statement := by
  intro S a ha
  refine ⟨paper_xi_time_part69d_localized_solenoid_endomorphism_ring S, ⟨?_, ?_⟩⟩
  · intro n hn
    have hPeriodic := paper_xi_localized_solenoid_periodic_point_formula S a ha n hn
    simpa [xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta_fixedPointCount] using
      hPeriodic.2.2.1
  · intro n hn
    have hCount :
        xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta_fixedPointCount S a n =
          localizedIndex S (a ^ n - 1) := by
      have hPeriodic := paper_xi_localized_solenoid_periodic_point_formula S a ha n hn
      simpa [xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta_fixedPointCount] using
        hPeriodic.2.2.1
    simp [xi_time_part69_localized_rational_endomorphism_fixedpoints_zeta_artinMazurCoefficient,
      hCount]

end

end Omega.Zeta
