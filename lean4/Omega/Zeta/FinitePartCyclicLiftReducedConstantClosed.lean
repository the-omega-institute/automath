namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the closed formula for reduced cyclic-lift
    constants in the ETDS finite-part section.
    thm:finite-part-cyclic-lift-reduced-constant-closed -/
theorem paper_etds_finite_part_cyclic_lift_reduced_constant_closed
    {Matrix : Type}
    (cyclicLiftConstant productClosedForm psi logarithmicClosedForm :
      Matrix → ℕ → ℝ)
    (closedFormToPsi :
      ∀ {A : Matrix} {q : ℕ},
        cyclicLiftConstant A q = productClosedForm A q →
          psi A q = logarithmicClosedForm A q)
    {A : Matrix} {q : ℕ}
    (hclosed : cyclicLiftConstant A q = productClosedForm A q) :
    cyclicLiftConstant A q = productClosedForm A q ∧
      psi A q = logarithmicClosedForm A q := by
  exact ⟨hclosed, closedFormToPsi hclosed⟩

end Omega.Zeta
