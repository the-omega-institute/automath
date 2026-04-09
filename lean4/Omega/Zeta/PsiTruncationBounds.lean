import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Zeta.PsiTruncationBounds

open Real

/-- `ψ(x) := -x - log(1-x)`.
    prop:finite-part-logM-gap-truncation-bounds -/
noncomputable def psi (x : ℝ) : ℝ := -x - Real.log (1 - x)

/-- For `x ∈ (0,1)`, `x < -log(1-x)`.
    cor:finite-part-logM-gap-positive -/
theorem neg_log_one_sub_gt (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) :
    x < -Real.log (1 - x) := by
  have h2 : (0 : ℝ) < 1 - x := by linarith
  have hne : (1 - x) ≠ 1 := by linarith
  have hlt := Real.log_lt_sub_one_of_pos h2 hne
  linarith

/-- Strict positivity of `ψ` on `(0,1)`.
    cor:finite-part-logM-gap-positive -/
theorem psi_pos (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) : 0 < psi x := by
  unfold psi
  have := neg_log_one_sub_gt x hx₀ hx₁
  linarith

/-- Weak upper bound: `-log(1-x) ≤ x/(1-x)` for `x ∈ [0,1)`.
    prop:finite-part-logM-gap-truncation-bounds -/
theorem neg_log_one_sub_le_div (x : ℝ) (_hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    -Real.log (1 - x) ≤ x / (1 - x) := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hinv : (0 : ℝ) < (1 - x)⁻¹ := inv_pos.mpr hpos
  have hle : Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at hle
  have hne : (1 - x) ≠ 0 := ne_of_gt hpos
  have hdiv : (1 - x)⁻¹ - 1 = x / (1 - x) := by
    field_simp
    ring
  linarith [hle, hdiv]

/-- Weak upper bound: `ψ(x) ≤ x²/(1-x)` for `x ∈ [0,1)`.
    prop:finite-part-logM-gap-truncation-bounds -/
theorem psi_le_weak (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    psi x ≤ x ^ 2 / (1 - x) := by
  unfold psi
  have h := neg_log_one_sub_le_div x hx₀ hx₁
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hne : (1 - x) ≠ 0 := ne_of_gt hpos
  have hid : x ^ 2 / (1 - x) = -x + x / (1 - x) := by
    field_simp
    ring
  linarith [h, hid]

/-- Paper package (positivity).
    cor:finite-part-logM-gap-positive -/
theorem paper_finite_part_gap_positive (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) :
    0 < psi x := psi_pos x hx₀ hx₁

/-- Paper package (weak truncation bound).
    prop:finite-part-logM-gap-truncation-bounds -/
theorem paper_finite_part_gap_truncation_bounds (x : ℝ)
    (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    psi x ≤ x ^ 2 / (1 - x) := psi_le_weak x hx₀ hx₁

end Omega.Zeta.PsiTruncationBounds
