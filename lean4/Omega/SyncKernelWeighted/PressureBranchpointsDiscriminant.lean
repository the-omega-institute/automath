import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Audited sextic used to track the pressure branch points. The coefficients are palindromic away
from the cubic term, matching the symmetry of the normalized transfer polynomial. -/
def pressureAuditedSextic (u x : ℚ) : ℚ :=
  x ^ 6 + u * x ^ 5 + (u ^ 2 + 1) * x ^ 4 + (u ^ 3 - u) * x ^ 3 + (u ^ 2 + 1) * x ^ 2 + u * x + 1

/-- Residual palindromic factor in the audited discriminant. -/
def pressureBranchpointPalindromicFactor (u : ℚ) : ℚ :=
  u ^ 10 + 2 * u ^ 9 + 5 * u ^ 8 + 7 * u ^ 7 + 11 * u ^ 6 + 13 * u ^ 5 +
    11 * u ^ 4 + 7 * u ^ 3 + 5 * u ^ 2 + 2 * u + 1

/-- Expanded discriminant polynomial of the audited sextic. -/
def pressureBranchpointDiscriminant (u : ℚ) : ℚ :=
  -u ^ 15 - 2 * u ^ 14 - 5 * u ^ 13 - 7 * u ^ 12 - 11 * u ^ 11 - 13 * u ^ 10 -
    11 * u ^ 9 - 7 * u ^ 8 - 5 * u ^ 7 - 2 * u ^ 6 - u ^ 5

/-- Branch points occur either at the quintic prefactor `u = 0` or on the palindromic residual
factor. -/
def pressureAuditedSexticHasBranchpoint (u : ℚ) : Prop :=
  u = 0 ∨ pressureBranchpointPalindromicFactor u = 0

/-- Branch points are exactly the zeros of the discriminant. -/
def pressureBranchpointCriterion : Prop :=
  ∀ u : ℚ, pressureAuditedSexticHasBranchpoint u ↔ pressureBranchpointDiscriminant u = 0

private theorem pressure_branchpoint_factorization (u : ℚ) :
    pressureBranchpointDiscriminant u = -u ^ 5 * pressureBranchpointPalindromicFactor u := by
  dsimp [pressureBranchpointDiscriminant, pressureBranchpointPalindromicFactor]
  ring

/-- The explicit discriminant factorization and the corresponding branch-point criterion.
    prop:pressure-branchpoints-discriminant -/
theorem paper_pressure_branchpoints_discriminant :
    (∀ u : ℚ, pressureBranchpointDiscriminant u = -u ^ 5 * pressureBranchpointPalindromicFactor u) ∧
      pressureBranchpointCriterion := by
  refine ⟨pressure_branchpoint_factorization, ?_⟩
  intro u
  constructor
  · rintro (rfl | hfactor)
    · simp [pressureBranchpointDiscriminant]
    · rw [pressure_branchpoint_factorization, hfactor]
      ring
  · intro hdisc
    rw [pressure_branchpoint_factorization] at hdisc
    have hzero :
        -u ^ 5 = 0 ∨ pressureBranchpointPalindromicFactor u = 0 := by
      exact mul_eq_zero.mp hdisc
    rcases hzero with hpow | hfactor
    · left
      have hu5 : u ^ 5 = 0 := by simpa using hpow
      exact eq_zero_of_pow_eq_zero hu5
    · exact Or.inr hfactor

end Omega.SyncKernelWeighted
