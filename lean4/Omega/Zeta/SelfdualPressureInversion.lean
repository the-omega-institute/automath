import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Zeta

/-- Paper label: `cor:xi-selfdual-pressure-inversion`. -/
theorem paper_xi_selfdual_pressure_inversion (lambda P : ℝ → ℝ)
    (hPos : ∀ u : ℝ, 0 < u → 0 < lambda u)
    (hInv : ∀ u : ℝ, 0 < u → lambda u = u * lambda (1 / u))
    (hLog : ∀ u : ℝ, 0 < u → P u = Real.log (lambda u)) :
    ∀ u : ℝ,
      0 < u → lambda u = u * lambda (1 / u) ∧ P u = Real.log u + P (1 / u) := by
  intro u hu
  have huInv : 0 < 1 / u := one_div_pos.mpr hu
  have hLambdaInv : 0 < lambda (1 / u) := hPos (1 / u) huInv
  refine ⟨hInv u hu, ?_⟩
  rw [hLog u hu, hInv u hu, Real.log_mul hu.ne' hLambdaInv.ne', hLog (1 / u) huInv]

end Omega.Zeta
