import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

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

/-- Paper package (sharp truncation bounds).
    prop:finite-part-logM-gap-truncation-bounds -/
theorem paper_finite_part_logm_gap_truncation_bounds (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ 2 / 2 ≤ psi x ∧ psi x ≤ x ^ 2 / (2 * (1 - x)) := by
  have hx0' : 0 ≤ x := hx0.le
  have hgap : 0 < 1 - x := by linarith
  have hgap_ne : 1 - x ≠ 0 := ne_of_gt hgap
  let u : ℝ := x / (2 - x)
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg hx0' (by linarith : 0 ≤ 2 - x)
  have hu_lt_one : u < 1 := by
    dsimp [u]
    rw [div_lt_one (by linarith : 0 < 2 - x)]
    linarith
  have hlog_arg : 1 + x / (1 - x) = (1 - x)⁻¹ := by
    field_simp [hgap_ne]
    ring
  have hlog_eq : Real.log (1 + x / (1 - x)) = -Real.log (1 - x) := by
    rw [hlog_arg, Real.log_inv]
  constructor
  · have hx_div_nonneg : 0 ≤ x / (1 - x) := div_nonneg hx0' hgap.le
    have hfirst := Real.le_log_one_add_of_nonneg hx_div_nonneg
    have hfirst' :
        2 * (x / (1 - x)) / (x / (1 - x) + 2) ≤ -Real.log (1 - x) := by
      simpa [hlog_eq] using hfirst
    have halg :
        x + x ^ 2 / 2 ≤ 2 * (x / (1 - x)) / (x / (1 - x) + 2) := by
      field_simp [hgap_ne]
      nlinarith [hx0, hx1]
    unfold psi
    linarith
  · have hx_div_nonneg : 0 ≤ x / (1 - x) := div_nonneg hx0' hgap.le
    have hu_eq : x / (1 - x) / (x / (1 - x) + 2) = u := by
      dsimp [u]
      have hden_ne : x / (1 - x) + 2 ≠ 0 := by positivity
      have htwo_ne : 2 - x ≠ 0 := by linarith
      field_simp [hgap_ne, hden_ne, htwo_ne]
      ring
    have hseries :
        HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * u ^ (2 * k + 1))
          (-Real.log (1 - x)) := by
      have h := Real.hasSum_log_one_add hx_div_nonneg
      rw [hlog_eq] at h
      simpa [hu_eq] using h
    have hu_sq_lt_one : u ^ 2 < 1 := by
      nlinarith [hu_nonneg, hu_lt_one]
    have hgeom :
        HasSum (fun k : ℕ => (2 * u) * (u ^ 2) ^ k) ((2 * u) * (1 - u ^ 2)⁻¹) :=
      (hasSum_geometric_of_lt_one (sq_nonneg u) hu_sq_lt_one).mul_left (2 * u)
    have hgeom' : HasSum (fun k : ℕ => (2 : ℝ) * u ^ (2 * k + 1))
        (2 * u / (1 - u ^ 2)) := by
      convert hgeom using 1
      · ext k
        rw [show 2 * k + 1 = Nat.succ (2 * k) by omega, pow_succ, pow_mul]
        ring
    have hterm :
        ∀ k : ℕ, (2 : ℝ) * (1 / (2 * k + 1)) * u ^ (2 * k + 1) ≤
          2 * u ^ (2 * k + 1) := by
      intro k
      have hcoef : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
        rw [div_le_one (by positivity : (0 : ℝ) < 2 * k + 1)]
        norm_num
      have hpow : 0 ≤ u ^ (2 * k + 1) := pow_nonneg hu_nonneg _
      nlinarith
    have hupper_log : -Real.log (1 - x) ≤ 2 * u / (1 - u ^ 2) :=
      hasSum_le hterm hseries hgeom'
    have halg : 2 * u / (1 - u ^ 2) = x + x ^ 2 / (2 * (1 - x)) := by
      have hu_denom_pos : 0 < 1 - u ^ 2 := by nlinarith [hu_sq_lt_one]
      have htwo_ne : 2 - x ≠ 0 := by linarith
      rw [div_eq_iff hu_denom_pos.ne']
      dsimp [u]
      field_simp [hgap_ne, htwo_ne]
      ring
    unfold psi
    rw [halg] at hupper_log
    linarith

end Omega.Zeta.PsiTruncationBounds
