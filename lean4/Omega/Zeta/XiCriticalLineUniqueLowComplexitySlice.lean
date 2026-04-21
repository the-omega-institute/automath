import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.RadialInformationProjectionLowerBound


namespace Omega.Zeta

open Omega.TypedAddressBiaxialCompletion

/-- A uniformly bounded certified radial readout budget forces the `xi` slice to stay on the
critical line. Off the critical line, the radial parameter grows like `log L`, so the lower bound
from the typed-address completion package eventually exceeds any fixed complexity cap.
    cor:xi-critical-line-unique-low-complexity-slice -/
theorem paper_xi_critical_line_unique_low_complexity_slice (σ ε : ℝ) (N : ℕ) (hε : 0 < ε)
    (hbounded : ∀ L : ℝ, 1 < L → ∃ n ≤ N,
      Omega.TypedAddressBiaxialCompletion.xiCertifiedRadialReadout ((2 * σ - 1) * Real.log L) ε n) :
    σ = 1 / 2 := by
  by_contra hσ
  let a : ℝ := 2 * σ - 1
  have ha : a ≠ 0 := by
    intro ha0
    apply hσ
    dsimp [a] at ha0
    linarith
  have haabs : 0 < |a| := abs_pos.mpr ha
  let B : ℝ := ε * (2 : ℝ) ^ N / Real.pi
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  let y : ℝ := (B + 1) / |a|
  have hypos : 0 < y := by
    dsimp [y]
    positivity
  let L : ℝ := Real.exp y
  have hL : 1 < L := by
    dsimp [L]
    simpa using Real.one_lt_exp_iff.mpr hypos
  obtain ⟨n, hnN, hcert⟩ := hbounded L hL
  have hLower :
      Real.logb 2 (xiJacobianAmplification (a * Real.log L) / ε) ≤ n :=
    paper_xi_radial_information_projection_lower_bound (a * Real.log L) ε n hε hcert
  have hAbs :
      |a * Real.log L| = B + 1 := by
    dsimp [L]
    rw [Real.log_exp, abs_mul, abs_of_pos hypos]
    dsimp [y]
    field_simp [haabs.ne']
  have hSq :
      (a * Real.log L) ^ 2 = (B + 1) ^ 2 := by
    have hSqAbs : |a * Real.log L| ^ 2 = (B + 1) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hAbs
    calc
      (a * Real.log L) ^ 2 = |a * Real.log L| ^ 2 := by rw [sq_abs]
      _ = (B + 1) ^ 2 := hSqAbs
  have hLarge :
      (2 : ℝ) ^ N < xiJacobianAmplification (a * Real.log L) / ε := by
    have hBlt : B < 1 + (B + 1) ^ 2 := by
      nlinarith [hBpos]
    have hscale :
        (Real.pi / ε) * B < (Real.pi / ε) * (1 + (B + 1) ^ 2) := by
      have hpiε : 0 < Real.pi / ε := by positivity
      gcongr
    have hrewrite :
        (Real.pi / ε) * (1 + (B + 1) ^ 2) =
          xiJacobianAmplification (a * Real.log L) / ε := by
      rw [xiJacobianAmplification, hSq]
      ring
    calc
      (2 : ℝ) ^ N = (Real.pi / ε) * B := by
        dsimp [B]
        field_simp [hε.ne', Real.pi_ne_zero]
      _ < (Real.pi / ε) * (1 + (B + 1) ^ 2) := hscale
      _ = xiJacobianAmplification (a * Real.log L) / ε := hrewrite
  have hRatioPos : 0 < xiJacobianAmplification (a * Real.log L) / ε := by
    exact div_pos (xiJacobianAmplification_pos _) hε
  have hNlt :
      (N : ℝ) < Real.logb 2 (xiJacobianAmplification (a * Real.log L) / ε) := by
    exact (Real.lt_logb_iff_rpow_lt (b := (2 : ℝ)) (by norm_num) hRatioPos).2 <| by
      simpa [Real.rpow_natCast] using hLarge
  have hnle : (n : ℝ) ≤ N := by
    exact_mod_cast hnN
  have : (N : ℝ) < N := lt_of_lt_of_le (lt_of_lt_of_le hNlt hLower) hnle
  linarith

end Omega.Zeta
