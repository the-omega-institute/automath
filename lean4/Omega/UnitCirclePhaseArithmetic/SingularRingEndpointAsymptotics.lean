import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The explicit singular-ring zero `t_{n,k} = -1 / (4 cos^2 (π k / n))`. -/
def singular_ring_endpoint_asymptotics_zero (n k : ℕ) : ℝ :=
  -(1 / (4 * Real.cos (Real.pi * k / n) ^ 2))

/-- Paper label: `lem:singular-ring-endpoint-asymptotics`.
Starting from the explicit zero formula, the first endpoint is obtained by direct substitution,
while the most negative endpoint reduces to a sine square by the identities
`cos (π / 2 - x) = sin x`, with separate odd/even index formulas. -/
theorem paper_singular_ring_endpoint_asymptotics (n : ℕ) (hn : 2 ≤ n) :
    singular_ring_endpoint_asymptotics_zero n 1 =
      -(1 / (4 * Real.cos (Real.pi / n) ^ 2)) ∧
      ((Odd n →
          singular_ring_endpoint_asymptotics_zero n ((n - 1) / 2) =
            -(1 / (4 * Real.sin (Real.pi / (2 * n)) ^ 2))) ∧
        (Even n →
          singular_ring_endpoint_asymptotics_zero n (n / 2 - 1) =
            -(1 / (4 * Real.sin (Real.pi / n) ^ 2)))) := by
  refine ⟨by simp [singular_ring_endpoint_asymptotics_zero], ?_⟩
  refine ⟨?_, ?_⟩
  · intro hodd
    rcases hodd with ⟨k, rfl⟩
    have hidx : ((2 * k + 1 - 1) / 2 : ℕ) = k := by omega
    have hangle :
        (Real.pi : ℝ) * (k : ℝ) / (2 * k + 1 : ℕ) =
          Real.pi / 2 - Real.pi / (2 * (2 * k + 1 : ℕ)) := by
      field_simp [Real.pi_ne_zero]
      ring_nf
      norm_num
    rw [singular_ring_endpoint_asymptotics_zero, hidx, hangle, Real.cos_pi_div_two_sub]
  · intro heven
    rcases heven with ⟨k, rfl⟩
    have hk : 1 ≤ k := by omega
    have hidx : (((k + k : ℕ) / 2) - 1) = k - 1 := by omega
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
    have hangle :
        (Real.pi : ℝ) * ((k - 1 : ℕ) : ℝ) / (k + k : ℕ) =
          Real.pi / 2 - Real.pi / (k + k : ℕ) := by
      rw [Nat.cast_sub hk]
      field_simp [hk_pos.ne', Real.pi_ne_zero]
      rw [Nat.cast_add]
      ring
    rw [singular_ring_endpoint_asymptotics_zero, hidx, hangle, Real.cos_pi_div_two_sub]

end

end Omega.UnitCirclePhaseArithmetic
