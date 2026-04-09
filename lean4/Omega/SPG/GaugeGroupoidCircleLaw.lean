import Mathlib.Tactic

/-!
# Gauge groupoid circle law seed values

Arithmetic identities for the boundary gauge groupoid circle dimension index law.
-/

namespace Omega.SPG

/-- Gauge groupoid circle law seeds.
    thm:spg-boundary-gauge-groupoid-circle-law -/
theorem paper_spg_boundary_gauge_groupoid_circle_law_seeds :
    (1 - 1 = 0) ∧
    (2 - 1 = 1) ∧
    (0 - 1 = (-1 : ℤ)) ∧
    (∀ n : Nat, 0 < n → n ^ 0 = 1) ∧
    (3 - 3 + 1 = 1) ∧
    (6 / 2 = 3) := by
  exact ⟨by omega, by omega, by omega, fun _ _ => pow_zero _, by omega, by omega⟩

end Omega.SPG
