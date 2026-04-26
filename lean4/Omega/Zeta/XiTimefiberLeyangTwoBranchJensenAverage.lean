import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-timefiber-leyang-two-branch-jensen-average`.
Pairing the angular samples at `θ` and `-θ` turns the audited log-modulus into the average of
the two explicit Lee--Yang branches `t₊ = ρ cos θ + |sin θ|` and
`t₋ = ρ cos θ - |sin θ|`. -/
theorem paper_xi_timefiber_leyang_two_branch_jensen_average (ρ θ : ℝ) :
    let angularLogMod := fun φ : ℝ => Real.log |1 + ρ * Real.cos φ + Real.sin φ|
    let tPlus : ℝ := ρ * Real.cos θ + |Real.sin θ|
    let tMinus : ℝ := ρ * Real.cos θ - |Real.sin θ|
    (angularLogMod θ + angularLogMod (-θ)) / 2 =
      (Real.log |1 + tPlus| + Real.log |1 + tMinus|) / 2 := by
  dsimp
  have hcos : Real.cos (-θ) = Real.cos θ := by
    simp
  have hsin_neg : Real.sin (-θ) = -Real.sin θ := by
    simp
  by_cases hsin : 0 ≤ Real.sin θ
  · have habs : |Real.sin θ| = Real.sin θ := abs_of_nonneg hsin
    simp [hcos, hsin_neg, habs, sub_eq_add_neg, add_assoc]
  · have habs : |Real.sin θ| = -Real.sin θ := abs_of_neg (lt_of_not_ge hsin)
    simp [hcos, hsin_neg, habs, sub_eq_add_neg, add_assoc, add_comm]

end Omega.Zeta
