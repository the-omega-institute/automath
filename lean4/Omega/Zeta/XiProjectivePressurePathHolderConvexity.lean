import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic
import Omega.Zeta.XiTimePart50dcProjectivePressurePerronLogconvex

namespace Omega.Zeta

/-- A concrete path-radius certificate obtained from one affine path weight at the integer order
`q`. -/
noncomputable def xi_projective_pressure_path_holder_convexity_path_radius
    (n : ℕ) (offset slope : Fin (n + 1) → ℝ) (q : ℝ) (i : Fin (n + 1)) : ℝ :=
  Real.exp (xiAffinePathWeight offset slope q i)

/-- Paper label: `thm:xi-projective-pressure-path-holder-convexity`.
In the finite affine-path model of the projective pressure, the pressure is midpoint convex, the
associated Perron radius is midpoint log-convex, and every integer-order path certificate lies
below the full pressure profile. -/
theorem paper_xi_projective_pressure_path_holder_convexity
    (n : ℕ) (offset slope : Fin (n + 1) → ℝ) :
    (∀ q₀ q₁ : ℝ,
      xiProjectivePressure n offset slope ((q₀ + q₁) / 2) ≤
        (xiProjectivePressure n offset slope q₀ + xiProjectivePressure n offset slope q₁) / 2) ∧
    (∀ q₀ q₁ : ℝ,
      xiPerronRadius n offset slope ((q₀ + q₁) / 2) ^ 2 ≤
        xiPerronRadius n offset slope q₀ * xiPerronRadius n offset slope q₁) ∧
    (∀ q : ℕ, 2 ≤ q →
      ∀ i : Fin (n + 1),
        Real.log (xi_projective_pressure_path_holder_convexity_path_radius n offset slope (q : ℝ) i) ≤
          xiProjectivePressure n offset slope q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q₀ q₁
    exact (paper_xi_time_part50dc_projective_pressure_perron_logconvex n offset slope q₀ q₁).1
  · intro q₀ q₁
    exact (paper_xi_time_part50dc_projective_pressure_perron_logconvex n offset slope q₀ q₁).2
  · intro q _hq i
    rw [xi_projective_pressure_path_holder_convexity_path_radius, Real.log_exp]
    exact Finset.le_sup' (s := Finset.univ) (f := xiAffinePathWeight offset slope (q : ℝ))
      (Finset.mem_univ i)

end Omega.Zeta
