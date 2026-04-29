import Mathlib.Tactic
import Omega.Zeta.XiLocalizedSolenoidPeriodicPointFormula

namespace Omega.Zeta

/-- Concrete localized-solenoid data for the max-scale periodic-growth wrapper. The numerator and
denominator scales enter only through their maximum, matching the paper's dominant exponential
growth term. -/
structure xi_localized_solenoid_periodic_growth_max_scale_data where
  S : FinitePrimeLocalization
  a : ℕ
  b : ℕ
  hscale : 2 ≤ max a b

namespace xi_localized_solenoid_periodic_growth_max_scale_data

/-- Dominant scale `max {|a|, |b|}` in the chapter-local natural-number model. -/
def max_scale (D : xi_localized_solenoid_periodic_growth_max_scale_data) : ℕ :=
  max D.a D.b

/-- Fixed-point model used for the periodic-growth statement. -/
abbrev F_n (D : xi_localized_solenoid_periodic_growth_max_scale_data) (n : ℕ) :=
  xi_localized_solenoid_periodic_point_formula_fixModel D.S D.max_scale n

/-- Finite `S`-part bookkeeping term: the number of localized primes dividing the iterate index. -/
def s_part_valuation_bound (D : xi_localized_solenoid_periodic_growth_max_scale_data)
    (n : ℕ) : ℕ :=
  (D.S.filter fun p => p ∣ n).card

/-- The periodic-point count is exactly the localized quotient ledger evaluated at the dominant
max-scale iterate. -/
def log_growth_formula (D : xi_localized_solenoid_periodic_growth_max_scale_data) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    Nat.card (D.F_n n) = localizedIndex D.S (D.max_scale ^ n - 1)

/-- The finite periodic-point count is bounded above by the dominant max-scale exponential. -/
def growth_limit (D : xi_localized_solenoid_periodic_growth_max_scale_data) : Prop :=
  ∀ n : ℕ, 1 ≤ n → Nat.card (D.F_n n) ≤ D.max_scale ^ n

end xi_localized_solenoid_periodic_growth_max_scale_data

open xi_localized_solenoid_periodic_growth_max_scale_data

/-- Paper label: `thm:xi-localized-solenoid-periodic-growth-max-scale`.
The periodic-point formula identifies the fixed-point count with the localized quotient index of
`max {|a|, |b|} ^ n - 1`, and that finite index is always bounded by the dominant exponential
scale `max {|a|, |b|} ^ n`. -/
theorem paper_xi_localized_solenoid_periodic_growth_max_scale
    (D : xi_localized_solenoid_periodic_growth_max_scale_data) :
    D.log_growth_formula ∧ D.growth_limit := by
  refine ⟨?_, ?_⟩
  · intro n hn
    have hPeriodic :=
      paper_xi_localized_solenoid_periodic_point_formula D.S D.max_scale D.hscale n hn
    simpa [xi_localized_solenoid_periodic_growth_max_scale_data.F_n,
      xi_localized_solenoid_periodic_growth_max_scale_data.max_scale] using hPeriodic.2.2.1
  · intro n hn
    have hPeriodic :=
      paper_xi_localized_solenoid_periodic_point_formula D.S D.max_scale D.hscale n hn
    have hFormula : Nat.card (D.F_n n) = localizedIndex D.S (D.max_scale ^ n - 1) := by
      simpa [xi_localized_solenoid_periodic_growth_max_scale_data.F_n,
        xi_localized_solenoid_periodic_growth_max_scale_data.max_scale] using hPeriodic.2.2.1
    rw [hFormula]
    by_cases hmem : D.max_scale ^ n - 1 ∈ D.S
    · simp [localizedIndex, nSperp, hmem]
      have hscale_pos : 0 < D.max_scale := by
        exact lt_of_lt_of_le (by decide : 0 < 2) D.hscale
      exact Nat.succ_le_of_lt (pow_pos hscale_pos n)
    · simp [localizedIndex, nSperp, hmem]

end Omega.Zeta
