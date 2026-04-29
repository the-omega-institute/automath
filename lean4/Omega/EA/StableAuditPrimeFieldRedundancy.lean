import Mathlib.Tactic

namespace Omega.EA

/-- The prime fields used by the legacy two-variable linear audit. -/
def stable_audit_prime_field_redundancy_primes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/-- New separating ordered pairs first found at each listed prime. -/
def stable_audit_prime_field_redundancy_new_counts : List ℕ :=
  [439263, 90422, 56259, 20008, 2612, 384, 0, 0, 0, 0, 0]

/-- The cumulative legacy audit count through a prime bound `p`. -/
def stable_audit_prime_field_redundancy_cumulative (p : ℕ) : ℕ :=
  ((stable_audit_prime_field_redundancy_primes.zip
      stable_audit_prime_field_redundancy_new_counts).filter (fun qn => qn.1 ≤ p)).map
    Prod.snd |>.sum

/-- Later listed primes at which the cumulative count is unchanged. -/
def stable_audit_prime_field_redundancy_later_primes : List ℕ :=
  [17, 19, 23, 29, 31]

/-- Number of equations in the legacy at-most-two-variable prime-field audit. -/
def stable_audit_prime_field_redundancy_legacy_equation_count : ℕ := 810

/-- Prime bound in the legacy audit. -/
def stable_audit_prime_field_redundancy_legacy_prime_bound : ℕ := 31

/-- Number of equations in the stronger existing `_364` prime-field baseline. -/
def stable_audit_prime_field_redundancy_baseline_equation_count : ℕ := 4694

/-- Prime bound in the stronger existing `_364` prime-field baseline. -/
def stable_audit_prime_field_redundancy_baseline_prime_bound : ℕ := 199

/-- Numeric inclusion of the legacy audit scope in the stronger existing baseline certificate. -/
def stable_audit_prime_field_redundancy_legacy_scope_in_baseline : Prop :=
  stable_audit_prime_field_redundancy_legacy_equation_count ≤
      stable_audit_prime_field_redundancy_baseline_equation_count ∧
    stable_audit_prime_field_redundancy_legacy_prime_bound ≤
      stable_audit_prime_field_redundancy_baseline_prime_bound

/-- Paper-facing redundancy statement for the legacy prime-field audit. -/
def stable_audit_prime_field_redundancy_statement : Prop :=
  stable_audit_prime_field_redundancy_legacy_equation_count = 810 ∧
    stable_audit_prime_field_redundancy_cumulative 13 = 608948 ∧
    (∀ p ∈ stable_audit_prime_field_redundancy_later_primes,
      stable_audit_prime_field_redundancy_cumulative p = 608948) ∧
    stable_audit_prime_field_redundancy_legacy_scope_in_baseline

/-- Paper label: `prop:stable-audit-prime-field-redundancy`. -/
theorem paper_stable_audit_prime_field_redundancy :
    stable_audit_prime_field_redundancy_statement := by
  simp [stable_audit_prime_field_redundancy_statement,
    stable_audit_prime_field_redundancy_legacy_scope_in_baseline,
    stable_audit_prime_field_redundancy_legacy_equation_count,
    stable_audit_prime_field_redundancy_baseline_equation_count,
    stable_audit_prime_field_redundancy_legacy_prime_bound,
    stable_audit_prime_field_redundancy_baseline_prime_bound,
    stable_audit_prime_field_redundancy_later_primes,
    stable_audit_prime_field_redundancy_cumulative,
    stable_audit_prime_field_redundancy_primes,
    stable_audit_prime_field_redundancy_new_counts]

end Omega.EA
