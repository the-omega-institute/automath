import Mathlib.Tactic
import Omega.Zeta.XiTimePart62debbFinitePrimeSupportLocalizedAxisThreshold

namespace Omega.Zeta

/-- A finite compact audit platform with `a` circle factors and `b` localized solenoid factors is
recorded only through its finite axis count in this seed model. -/
abbrev xiFiniteCircleSolenoidCompactLedger (a b : ℕ) :=
  xiLocalizedAxisLedger a b

/-- Its Pontryagin dual ledger is the corresponding finite-rank localized-axis ledger. -/
abbrev xiFiniteCircleSolenoidDualLedger (a b : ℕ) :=
  xiLocalizedAxisLedger a b

/-- Paper label: `thm:xi-time-part62debb-finite-circle-solenoid-dual-ledger-obstruction`.
After dualizing a finite product of circle and localized-solenoid factors, only `a + b` localized
axes remain. The existing finite-axis threshold theorem therefore rules out hosting more than
`a + b` independent prime directions, in particular the first `a + b + 1` prime generators. -/
theorem paper_xi_time_part62debb_finite_circle_solenoid_dual_ledger_obstruction
    (a b : ℕ) :
    Nonempty (xiFiniteCircleSolenoidCompactLedger a b ≃ xiFiniteCircleSolenoidDualLedger a b) ∧
      xiLocalizedAxisMinimalChannel a b = a + b ∧
      ¬ xiLocalizedAxisThreshold (a + b + 1) a b := by
  have hThreshold :=
    paper_xi_time_part62debb_finite_prime_support_localized_axis_threshold (a + b + 1) a b
  refine ⟨⟨Equiv.refl _⟩, hThreshold.1, ?_⟩
  rw [hThreshold.2.2.2]
  omega

end Omega.Zeta
