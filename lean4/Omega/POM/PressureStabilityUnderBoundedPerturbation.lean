import Omega.POM.BoundedPerturbationInvariance

namespace Omega.POM

/-- Paper label: `cor:pom-pressure-stability-under-bounded-perturbation`. -/
theorem paper_pom_pressure_stability_under_bounded_perturbation
    (a b : ℕ → ℝ) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) (ha : ∀ m, 0 < a m)
    (hlb : ∀ m, c * a m ≤ b m) (hub : ∀ m, b m ≤ C * a m) :
    ∀ m : ℕ,
      0 < m →
        (1 / (m : ℝ)) * Real.log c + (1 / (m : ℝ)) * Real.log (a m) ≤
            (1 / (m : ℝ)) * Real.log (b m) ∧
          (1 / (m : ℝ)) * Real.log (b m) ≤
            (1 / (m : ℝ)) * Real.log C + (1 / (m : ℝ)) * Real.log (a m) := by
  intro m hm
  exact paper_bounded_multiplicative_perturbation_scaled (a m) (b m) c C (m : ℝ) hc hC
    (ha m) (by exact_mod_cast hm) (hlb m) (hub m)

end Omega.POM
