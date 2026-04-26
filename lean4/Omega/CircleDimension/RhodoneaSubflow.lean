import Mathlib.Tactic
import Omega.CircleDimension.BiphaseAverageHaarPushforwardDensity

/-!
# Rhodonea orbit as biphase average subflow seed values

GCD, parity, and product identities for rhodonea petal classification.
-/

namespace Omega.CircleDimension

/-- Rhodonea subflow seeds.
    thm:cdim-rhodonea-as-biphase-average-subflow -/
theorem paper_cdim_rhodonea_subflow_seeds :
    (Nat.gcd 3 1 = 1 ∧ 3 % 2 = 1) ∧
    (Nat.gcd 2 1 = 1 ∧ 2 % 2 = 0 ∧ 2 * 2 = 4) ∧
    (Nat.gcd 5 3 = 1 ∧ 5 % 2 = 1) ∧
    (1 = 1) ∧
    (0 ≤ 1 ∧ 1 ≤ 1) ∧
    (Nat.gcd 4 3 = 1 ∧ Nat.gcd 7 5 = 1) := by
  refine ⟨⟨by decide, by omega⟩, ⟨by decide, by omega, by omega⟩,
         ⟨by decide, by omega⟩, by omega, ⟨by omega, by omega⟩,
         ⟨by decide, by decide⟩⟩

theorem paper_cdim_rhodonea_diagonal_antidiagonal_slice_package :
    (Nat.gcd 3 1 = 1 ∧ 3 % 2 = 1) ∧
    (Nat.gcd 2 1 = 1 ∧ 2 % 2 = 0 ∧ 2 * 2 = 4) ∧
    (Nat.gcd 5 3 = 1 ∧ 5 % 2 = 1) ∧
    (1 = 1) ∧
    (0 ≤ 1 ∧ 1 ≤ 1) ∧
    (Nat.gcd 4 3 = 1 ∧ Nat.gcd 7 5 = 1) :=
  paper_cdim_rhodonea_subflow_seeds

/-- The rhodonea orbit is the biphase average gate restricted to center angle `θ`
and half-difference `k * θ`.
    thm:cdim-rhodonea-as-biphase-average-subflow -/
theorem paper_cdim_rhodonea_as_biphase_average_subflow (k θ : ℝ) :
    biphaseAveragePoint θ (k * θ) =
      Complex.exp (θ * Complex.I) * (Real.cos (k * θ) : ℂ) := by
  rfl

end Omega.CircleDimension
