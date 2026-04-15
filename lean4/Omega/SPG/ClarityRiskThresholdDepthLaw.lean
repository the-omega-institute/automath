import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.SPG.BoundaryDimensionAeStabilization
import Omega.SPG.PrefixScanErrorBoundaryDimensionUpper

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing threshold inversion for the SPG clarity risk law: once the scan error is known
    to decay like `C * exp (-((1 - d) log λ) m)`, the minimal depth realizing the risk threshold
    `δ` is squeezed between the corresponding logarithmic lower and upper bounds.
    thm:spg-clarity-risk-threshold-depth-law -/
theorem paper_spg_clarity_risk_threshold_depth_law
    (lam d C delta : ℝ) (mDelta : ℕ)
    (hLam : 1 < lam) (hd : d < 1) (hC : 0 < C) (hDelta : 0 < delta)
    (hUpper : C * Real.exp (-((1 - d) * Real.log lam) * mDelta) ≤ delta)
    (hPrev : delta < C * Real.exp (-((1 - d) * Real.log lam) * (mDelta - 1))) :
    Real.log (C / delta) / ((1 - d) * Real.log lam) ≤ mDelta ∧
      (mDelta : ℝ) ≤ 1 + Real.log (C / delta) / ((1 - d) * Real.log lam) := by
  let a : ℝ := (1 - d) * Real.log lam
  have hlogLam : 0 < Real.log lam := by
    exact Real.log_pos hLam
  have ha : 0 < a := by
    dsimp [a]
    nlinarith
  have hUpperExp : Real.exp (-(a * mDelta)) ≤ delta / C := by
    rw [le_div_iff₀ hC]
    simpa [a, mul_comm, mul_left_comm, mul_assoc] using hUpper
  have hUpperLog : -(a * mDelta) ≤ Real.log (delta / C) := by
    have hLog := Real.log_le_log (Real.exp_pos _) hUpperExp
    simpa using hLog
  have hLowerMain : Real.log (C / delta) ≤ a * mDelta := by
    have hratio : Real.log (C / delta) = -Real.log (delta / C) := by
      rw [show C / delta = (delta / C)⁻¹ by field_simp]
      rw [Real.log_inv]
    linarith
  have hLower : Real.log (C / delta) / a ≤ mDelta := by
    rw [div_le_iff₀ ha]
    simpa [mul_comm] using hLowerMain
  have hPrevExp : delta / C < Real.exp (-(a * (mDelta - 1))) := by
    rw [div_lt_iff₀ hC]
    simpa [a, mul_comm, mul_left_comm, mul_assoc] using hPrev
  have hPrevLog : Real.log (delta / C) < -(a * (mDelta - 1)) := by
    have hLog := Real.log_lt_log (div_pos hDelta hC) hPrevExp
    simpa using hLog
  have hUpperMain : a * (mDelta - 1 : ℝ) < Real.log (C / delta) := by
    have hratio : Real.log (C / delta) = -Real.log (delta / C) := by
      rw [show C / delta = (delta / C)⁻¹ by field_simp]
      rw [Real.log_inv]
    linarith
  have hStep : (mDelta - 1 : ℝ) < Real.log (C / delta) / a := by
    rw [lt_div_iff₀ ha]
    simpa [mul_comm] using hUpperMain
  have hUpperBound : (mDelta : ℝ) ≤ 1 + Real.log (C / delta) / a := by
    linarith
  exact ⟨hLower, by simpa [a] using hUpperBound⟩

end Omega.SPG
