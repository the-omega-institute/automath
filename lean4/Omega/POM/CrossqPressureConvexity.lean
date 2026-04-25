import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-crossq-pressure-convexity`. Discrete convexity of the pressure sequence
translates to a log inequality for the Perron roots; exponentiating gives the cross-`q` Perron
root bound. -/
theorem paper_pom_crossq_pressure_convexity (τ r : ℕ → ℝ)
    (hconvex : ∀ q ≥ 1, 2 * τ q ≤ τ (q - 1) + τ (q + 1))
    (hlog : ∀ q, τ q = Real.log (r q)) (hrpos : ∀ q, 0 < r q) :
    ∀ q ≥ 1, r q ^ 2 ≤ r (q - 1) * r (q + 1) := by
  intro q hq
  have hτ := hconvex q hq
  rw [hlog q, hlog (q - 1), hlog (q + 1)] at hτ
  have hexp :
      Real.exp (2 * Real.log (r q)) ≤ Real.exp (Real.log (r (q - 1)) + Real.log (r (q + 1))) :=
    Real.exp_le_exp.mpr hτ
  have hleft : Real.exp (2 * Real.log (r q)) = r q ^ 2 := by
    calc
      Real.exp (2 * Real.log (r q)) = Real.exp (Real.log (r q) + Real.log (r q)) := by
        congr 1
        ring
      _ = Real.exp (Real.log (r q)) * Real.exp (Real.log (r q)) := by rw [Real.exp_add]
      _ = r q * r q := by simp [Real.exp_log (hrpos q)]
      _ = r q ^ 2 := by rw [pow_two]
  have hright : Real.exp (Real.log (r (q - 1)) + Real.log (r (q + 1))) = r (q - 1) * r (q + 1) := by
    calc
      Real.exp (Real.log (r (q - 1)) + Real.log (r (q + 1))) =
          Real.exp (Real.log (r (q - 1))) * Real.exp (Real.log (r (q + 1))) := by
            rw [Real.exp_add]
      _ = r (q - 1) * r (q + 1) := by
            rw [Real.exp_log (hrpos (q - 1)), Real.exp_log (hrpos (q + 1))]
  calc
    r q ^ 2 = Real.exp (2 * Real.log (r q)) := hleft.symm
    _ ≤ Real.exp (Real.log (r (q - 1)) + Real.log (r (q + 1))) := hexp
    _ = r (q - 1) * r (q + 1) := hright

end Omega.POM
