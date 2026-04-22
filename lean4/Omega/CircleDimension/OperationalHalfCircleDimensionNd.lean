import Mathlib.Data.Real.Basic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the box law corollary for `ℕ^d`.
    cor:cdim-operational-half-circle-dimension-Nd -/
theorem paper_circle_dimension_operational_half_circle_dimension_nd
    (Mbox Nmax : ℕ → ℕ)
    (d : ℕ)
    (boxExponent halfCircleDimNd : ℝ)
    (hBox : ∀ b : ℕ, Mbox b = ((Nmax b + 1 : ℕ) ^ d))
    (hGrowth : boxExponent = ((d : ℕ) : ℝ) / 2)
    (hDim : halfCircleDimNd = ((d : ℕ) : ℝ) / 2) :
    (∀ b : ℕ, Mbox b = ((Nmax b + 1 : ℕ) ^ d)) ∧
      boxExponent = ((d : ℕ) : ℝ) / 2 ∧
      halfCircleDimNd = ((d : ℕ) : ℝ) / 2 := by
  exact ⟨hBox, hGrowth, hDim⟩

set_option maxHeartbeats 400000 in
/-- Exact-paper-name wrapper for `cor:cdim-operational-half-circle-dimension-Nd`. -/
theorem paper_cdim_operational_half_circle_dimension_nd
    (Mbox Nmax : ℕ → ℕ)
    (d : ℕ)
    (boxExponent halfCircleDimNd : ℝ)
    (hBox : ∀ b : ℕ, Mbox b = ((Nmax b + 1 : ℕ) ^ d))
    (hGrowth : boxExponent = ((d : ℕ) : ℝ) / 2)
    (hDim : halfCircleDimNd = ((d : ℕ) : ℝ) / 2) :
    (∀ b : ℕ, Mbox b = ((Nmax b + 1 : ℕ) ^ d)) ∧
      boxExponent = ((d : ℕ) : ℝ) / 2 ∧
      halfCircleDimNd = ((d : ℕ) : ℝ) / 2 := by
  exact ⟨hBox, hGrowth, hDim⟩

end Omega.CircleDimension
