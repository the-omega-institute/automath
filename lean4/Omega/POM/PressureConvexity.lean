import Mathlib.Tactic
import Omega.Folding.MomentSum

/-! # Pressure convexity: log S_q(m) is convex in q

This file formalizes Proposition prop:pom-pressure-convexity: for each fixed m,
the function q ↦ log S_q(m) is convex. The discrete version states that
  S_{q+1}(m)² ≤ S_q(m) · S_{q+2}(m)
for all q, m ≥ 0.

## Proof strategy
We prove log-convexity of power sums using Cauchy–Schwarz in the form
  (∑ rᵢ)² ≤ (∑ fᵢ)(∑ gᵢ)  when rᵢ² = fᵢ · gᵢ
with rᵢ = d(x)^(q+1), fᵢ = d(x)^(2q), gᵢ = d(x)^(2(q+1)).
-/

namespace Omega.POM.PressureConvexity

open Finset

/-- Log-convexity of moment sums: S_{q+1}(m)² ≤ S_q(m) · S_{q+2}(m).
    This is the discrete convexity statement for the pressure function.
    prop:pom-pressure-convexity -/
theorem momentSum_sq_le_mul (q m : Nat) :
    momentSum (q + 1) m ^ 2 ≤ momentSum q m * momentSum (q + 2) m := by
  simp only [momentSum]
  -- Use (∑ r_i)² ≤ (∑ f_i)(∑ g_i) when r_i² = f_i · g_i
  -- with r_i = d^(q+1), f_i = d^q, g_i = d^(q+2)
  -- Check: r_i² = d^(2(q+1)) = d^(2q+2) and f_i · g_i = d^q · d^(q+2) = d^(2q+2) ✓
  apply sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro x _; exact Nat.zero_le _
  · intro x _; exact Nat.zero_le _
  · intro x _; ring

/-- Computable version: S_{q+1}(m)² ≤ S_q(m) · S_{q+2}(m) in terms of cMomentSum.
    prop:pom-pressure-convexity -/
theorem cMomentSum_sq_le_mul (q m : Nat) :
    cMomentSum (q + 1) m ^ 2 ≤ cMomentSum q m * cMomentSum (q + 2) m := by
  rw [cMomentSum_eq, cMomentSum_eq, cMomentSum_eq]
  exact momentSum_sq_le_mul q m

/-- Seed verification: S_3(4)² ≤ S_2(4) · S_4(4).
    prop:pom-pressure-convexity -/
theorem pressure_convexity_seed_q2_m4 :
    cMomentSum 3 4 ^ 2 ≤ cMomentSum 2 4 * cMomentSum 4 4 :=
  cMomentSum_sq_le_mul 2 4

/-- Seed verification: S_4(5)² ≤ S_3(5) · S_5(5).
    prop:pom-pressure-convexity -/
theorem pressure_convexity_seed_q3_m5 :
    cMomentSum 4 5 ^ 2 ≤ cMomentSum 3 5 * cMomentSum 5 5 :=
  cMomentSum_sq_le_mul 3 5

/-- Paper wrapper: the pressure function P(q) = log r_q satisfies discrete convexity at
    adjacent integer points. In the finite-m version, this means S_{q+1}(m)² ≤ S_q(m)·S_{q+2}(m)
    holds for ALL q,m ∈ ℕ. Equivalently, q ↦ log S_q(m) is midpoint-convex.
    prop:pom-pressure-convexity -/
theorem paper_pressure_convexity (q m : Nat) :
    momentSum (q + 1) m ^ 2 ≤ momentSum q m * momentSum (q + 2) m :=
  momentSum_sq_le_mul q m

end Omega.POM.PressureConvexity
