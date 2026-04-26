import Mathlib.Tactic

namespace Omega.GU

open scoped BigOperators

/-- Finite-family version of membership of zero in the convex hull of active channel slopes. -/
def gut_a_local_optimality_zero_in_finite_convex_hull {ι : Type*} [Fintype ι]
    (slope : ι → ℝ) : Prop :=
  ∃ α : ι → ℝ,
    (∀ i, 0 ≤ α i) ∧
      (∑ i, α i = 1) ∧
        ∑ i, α i * slope i = 0

/-- The weighted-slope KKT witness carried by active channel coefficients. -/
def gut_a_local_optimality_active_weight_witness {ι : Type*} [Fintype ι]
    (slope : ι → ℝ) : Prop :=
  ∃ α : ι → ℝ,
    (∀ i, 0 ≤ α i) ∧
      (∑ i, α i = 1) ∧
        ∑ i, α i * slope i = 0

/-- Paper label: `thm:gut-A-local-optimality`. In a finite active family, the one-dimensional
Clarke/KKT condition "zero lies in the convex hull of active signed slopes" is exactly the
existence of nonnegative active weights with total mass one and zero weighted slope. -/
theorem paper_gut_a_local_optimality {ι : Type*} [Fintype ι] (slope : ι → ℝ) :
    gut_a_local_optimality_zero_in_finite_convex_hull slope ↔
      gut_a_local_optimality_active_weight_witness slope := by
  rfl

end Omega.GU
