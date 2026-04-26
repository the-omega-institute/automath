import Omega.Zeta.UnitaryDeterminantZeroUnitCircle

namespace Omega.Zeta

/-- Paper label: `thm:phase-lift-fixed-slice`. This extracts the fixed-slice consequence from
`paper_unitary_determinant_zero_unit_circle`; the paper's no-extra-register clause is semantic
packaging, while Lean only needs the determinant-zero implication. -/
theorem paper_phase_lift_fixed_slice {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : U.IsUnitary)
    {L : ℝ} (hL : 1 < L) :
    ∀ {s : ℂ}, Matrix.det (1 - ((L : ℂ) ^ (2 * s - 1)) • U) = 0 → s.re = 1 / 2 := by
  exact (paper_unitary_determinant_zero_unit_circle U hU).2 hL

end Omega.Zeta
