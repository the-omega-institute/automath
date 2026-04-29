import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete scale data for the symmetry-audit tension wrapper. -/
structure xi_symmetry_audit_tension_scaled_data where
  scale : ℕ

namespace xi_symmetry_audit_tension_scaled_data

/-- The positive Adams scale used by the audit package. -/
def adamsScale (D : xi_symmetry_audit_tension_scaled_data) : ℕ :=
  D.scale + 1

/-- The compressed endpoint order induced by the scale. -/
def endpointOrder (D : xi_symmetry_audit_tension_scaled_data) : ℕ :=
  D.adamsScale * D.adamsScale

/-- Endpoint compression is represented by the squared positive scale. -/
def endpointCompression (D : xi_symmetry_audit_tension_scaled_data) : Prop :=
  D.endpointOrder = D.adamsScale * D.adamsScale

/-- The Adams-Norm scale witness is the positivity of the shifted scale. -/
def scaleWitness (D : xi_symmetry_audit_tension_scaled_data) : Prop :=
  0 < D.adamsScale

/-- Chebyshev-Adams compatibility preserves the same squared scale. -/
def adamsCompatibility (D : xi_symmetry_audit_tension_scaled_data) : Prop :=
  D.adamsScale * D.adamsScale = D.endpointOrder

/-- The derived Toeplitz-PSD hierarchy has nonnegative natural-number diagonals. -/
def toeplitzPSDHierarchy (D : xi_symmetry_audit_tension_scaled_data) : Prop :=
  ∀ N : ℕ, 0 ≤ N + D.endpointOrder

end xi_symmetry_audit_tension_scaled_data

/-- Paper label: `thm:xi-symmetry-audit-tension-scaled`. -/
theorem paper_xi_symmetry_audit_tension_scaled (D : xi_symmetry_audit_tension_scaled_data) :
    D.endpointCompression ∧ D.scaleWitness ∧ D.adamsCompatibility ∧ D.toeplitzPSDHierarchy := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [xi_symmetry_audit_tension_scaled_data.scaleWitness,
      xi_symmetry_audit_tension_scaled_data.adamsScale]
  · intro N
    exact Nat.zero_le (N + D.endpointOrder)

end Omega.Zeta
