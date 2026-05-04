import Mathlib.Tactic

namespace Omega.Conclusion

/-- Greatest-lower-bound predicate for the integer pressure envelope sampled over `q ≥ 2`. -/
def conclusion_gauge_density_pressure_envelope_isGLB (Gamma : ℕ → ℝ) (envelope : ℝ) :
    Prop :=
  ∀ growth : ℝ, (∀ q : ℕ, 2 ≤ q → growth ≤ Gamma q) → growth ≤ envelope

/-- Paper label: `cor:conclusion-gauge-density-pressure-envelope`. -/
theorem paper_conclusion_gauge_density_pressure_envelope (growth envelope : Real)
    (Gamma : Nat -> Real) (hBound : forall q : Nat, 2 <= q -> growth <= Gamma q)
    (hGLB : conclusion_gauge_density_pressure_envelope_isGLB Gamma envelope) :
    growth <= envelope := by
  exact hGLB growth hBound

end Omega.Conclusion
