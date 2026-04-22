import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.SPG.GaugeGroupoidCircleLaw

namespace Omega.SPG

/-- Groupoid-cardinality contribution of the boundary gauge representation sector. -/
def spgBoundaryGaugeRepCard (G b₀ b₁ : ℕ) : ℕ :=
  G ^ (b₁ - b₀)

/-- Gauge-reduced boundary code capacity after adjoining the coarse label space `X`. -/
def spgBoundaryGaugeCodeCard (X G b₀ b₁ : ℕ) : ℕ :=
  X * spgBoundaryGaugeRepCard G b₀ b₁

/-- The coarse label count multiplies the circle-law groupoid cardinality, and any requirement to
cover all `2^n` microstates yields the corresponding logarithmic and Betti-number lower bounds.
    cor:spg-boundary-gauge-groupoid-capacity -/
theorem paper_spg_boundary_gauge_groupoid_capacity
    (n X G b₀ b₁ : ℕ) (hX : 0 < X) (hG : 1 < G) (hb : b₀ ≤ b₁) :
    spgBoundaryGaugeCodeCard X G b₀ b₁ = X * G ^ (b₁ - b₀) ∧
      (2 ^ n ≤ spgBoundaryGaugeCodeCard X G b₀ b₁ →
        (n : ℝ) * Real.log 2 ≤ Real.log X + ((b₁ - b₀ : ℕ) : ℝ) * Real.log G) ∧
      (2 ^ n ≤ spgBoundaryGaugeCodeCard X G b₀ b₁ →
        (b₀ : ℝ) + (((n : ℝ) * Real.log 2 - Real.log X) / Real.log G) ≤ b₁) := by
  have hlogBound :
      2 ^ n ≤ spgBoundaryGaugeCodeCard X G b₀ b₁ →
        (n : ℝ) * Real.log 2 ≤ Real.log X + ((b₁ - b₀ : ℕ) : ℝ) * Real.log G := by
    intro hCap
    have hCapR : (2 ^ n : ℝ) ≤ (spgBoundaryGaugeCodeCard X G b₀ b₁ : ℝ) := by
      exact_mod_cast hCap
    have hPow :
        (n : ℝ) * Real.log 2 ≤ Real.log (spgBoundaryGaugeCodeCard X G b₀ b₁ : ℝ) := by
      simpa [Real.log_pow] using
        (Real.le_log_of_pow_le (x := (2 : ℝ)) (n := n)
          (y := (spgBoundaryGaugeCodeCard X G b₀ b₁ : ℝ)) (by positivity) hCapR)
    have hX_ne : (X : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hX)
    have hG_ne : (G : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hG))
    rw [spgBoundaryGaugeCodeCard, spgBoundaryGaugeRepCard, Nat.cast_mul, Nat.cast_pow,
      Real.log_mul hX_ne (pow_ne_zero (b₁ - b₀) hG_ne), Real.log_pow] at hPow
    simpa using hPow
  have hlogG : 0 < Real.log G := by
    exact Real.log_pos (by exact_mod_cast hG)
  refine ⟨rfl, hlogBound, ?_⟩
  intro hCap
  have hMain := hlogBound hCap
  have hScaled :
      (n : ℝ) * Real.log 2 - Real.log X ≤ ((b₁ - b₀ : ℕ) : ℝ) * Real.log G := by
    linarith
  have hDiv : (((n : ℝ) * Real.log 2 - Real.log X) / Real.log G) ≤ ((b₁ - b₀ : ℕ) : ℝ) := by
    exact (div_le_iff₀ hlogG).2 hScaled
  rw [Nat.cast_sub hb] at hDiv
  linarith

end Omega.SPG
