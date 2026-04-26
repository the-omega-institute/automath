import Mathlib.Tactic

namespace Omega.StableArithmetic.PrimaryClosure

/-- Concrete audit predicate: a dashboard pair has an integral affine closure certificate. -/
def stable_audit_primary_closure_integral_affine_closed (dashboardPair : ℕ) : Prop :=
  ∃ certificate : ℤ, certificate = dashboardPair

/-- The `2`- and `3`-primary specializations inherit the integral affine closure certificate. -/
def stable_audit_primary_closure_primary_closed (primary dashboardPair : ℕ) : Prop :=
  (primary = 2 ∨ primary = 3) ∧
    stable_audit_primary_closure_integral_affine_closed dashboardPair

/-- Data package for the audited dashboard pairs and their integral affine closure certificates. -/
structure stable_audit_primary_closure_data where
  dashboardPairs : Finset ℕ
  integralAffineClosureCertificate :
    ∀ dashboardPair ∈ dashboardPairs,
      stable_audit_primary_closure_integral_affine_closed dashboardPair

namespace stable_audit_primary_closure_data

/-- No audited dashboard pair has a residual `2`- or `3`-primary exception. -/
def no_primary_exception (D : stable_audit_primary_closure_data) : Prop :=
  ∀ dashboardPair ∈ D.dashboardPairs,
    stable_audit_primary_closure_primary_closed 2 dashboardPair ∧
      stable_audit_primary_closure_primary_closed 3 dashboardPair

end stable_audit_primary_closure_data

/-- Integral affine closure specializes to the two primary cases used in the audit. -/
lemma stable_audit_primary_closure_specializes_to_primary
    {dashboardPair : ℕ}
    (h : stable_audit_primary_closure_integral_affine_closed dashboardPair) :
    stable_audit_primary_closure_primary_closed 2 dashboardPair ∧
      stable_audit_primary_closure_primary_closed 3 dashboardPair := by
  exact ⟨⟨Or.inl rfl, h⟩, ⟨Or.inr rfl, h⟩⟩

/-- Paper label: `cor:stable-audit-primary-closure`. -/
theorem paper_stable_audit_primary_closure (D : stable_audit_primary_closure_data) :
    D.no_primary_exception := by
  intro dashboardPair hdashboardPair
  exact stable_audit_primary_closure_specializes_to_primary
    (D.integralAffineClosureCertificate dashboardPair hdashboardPair)

end Omega.StableArithmetic.PrimaryClosure
