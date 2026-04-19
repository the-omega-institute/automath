import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.GU

/-- The logarithmic binary-to-Fibonacci rescaling slope `log_φ 2`. -/
noncomputable def terminalKmSlope : ℝ :=
  Real.log 2 / Real.log Real.goldenRatio

/-- Deterministic depth rescaling model for the terminal Fibonacci bracketing index. -/
noncomputable def terminalKmDepth (m : ℕ) : ℕ :=
  Nat.floor ((m : ℝ) * terminalKmSlope) + 1

private lemma log_goldenRatio_pos : 0 < Real.log Real.goldenRatio :=
  Real.log_pos Real.one_lt_goldenRatio

private lemma terminalKmSlope_nonneg : 0 ≤ terminalKmSlope := by
  unfold terminalKmSlope
  have hlog2 : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  exact div_nonneg hlog2 (le_of_lt log_goldenRatio_pos)

private lemma terminalKmSlope_lt_three_halves : terminalKmSlope < 3 / 2 := by
  unfold terminalKmSlope
  have hphi_gt : (8 / 5 : ℝ) < Real.goldenRatio := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  have hlogphi_gt : Real.log (8 / 5 : ℝ) < Real.log Real.goldenRatio :=
    Real.log_lt_log (by positivity) hphi_gt
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog85_pos : 0 < Real.log (8 / 5 : ℝ) := Real.log_pos (by norm_num)
  have haux :
      Real.log 2 / Real.log Real.goldenRatio < Real.log 2 / Real.log (8 / 5 : ℝ) := by
    exact (div_lt_div_iff_of_pos_left hlog2_pos log_goldenRatio_pos hlog85_pos).2 hlogphi_gt
  have hbound : Real.log 2 / Real.log (8 / 5 : ℝ) < 3 / 2 := by
    have hpow : (4 : ℝ) < (8 / 5 : ℝ) ^ 3 := by norm_num
    have hlog : Real.log 4 < Real.log ((8 / 5 : ℝ) ^ 3) := Real.log_lt_log (by positivity) hpow
    have hrewrite : 2 * Real.log 2 < 3 * Real.log (8 / 5 : ℝ) := by
      simpa [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_rpow] using hlog
    have hden : 0 < Real.log (8 / 5 : ℝ) := Real.log_pos (by norm_num)
    rw [div_lt_iff₀ hden]
    nlinarith
  exact lt_trans haux hbound

private lemma four_thirds_lt_terminalKmSlope : 4 / 3 < terminalKmSlope := by
  unfold terminalKmSlope
  have hphi_lt : Real.goldenRatio < (13 / 8 : ℝ) := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  have hlogphi_lt : Real.log Real.goldenRatio < Real.log (13 / 8 : ℝ) :=
    Real.log_lt_log Real.goldenRatio_pos hphi_lt
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog138_pos : 0 < Real.log (13 / 8 : ℝ) := Real.log_pos (by norm_num)
  have haux :
      Real.log 2 / Real.log (13 / 8 : ℝ) < Real.log 2 / Real.log Real.goldenRatio := by
    exact (div_lt_div_iff_of_pos_left hlog2_pos hlog138_pos log_goldenRatio_pos).2 hlogphi_lt
  have hbound : 4 / 3 < Real.log 2 / Real.log (13 / 8 : ℝ) := by
    have hpow : (13 / 8 : ℝ) ^ 4 < (8 : ℝ) := by norm_num
    have hlog : Real.log ((13 / 8 : ℝ) ^ 4) < Real.log 8 := Real.log_lt_log (by positivity) hpow
    have hrewrite : 4 * Real.log (13 / 8 : ℝ) < 3 * Real.log 2 := by
      simpa [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_rpow] using hlog
    have hden : 0 < Real.log (13 / 8 : ℝ) := Real.log_pos (by norm_num)
    rw [lt_div_iff₀ hden]
    nlinarith
  exact lt_trans hbound haux

private lemma terminalKmDepth_error_le_one (m : ℕ) :
    |(terminalKmDepth m : ℝ) - (m : ℝ) * terminalKmSlope| ≤ 1 := by
  unfold terminalKmDepth
  set x : ℝ := (m : ℝ) * terminalKmSlope
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le m) terminalKmSlope_nonneg
  have hfloor_le : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx_nonneg
  have hlt : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  have hnonneg : 0 ≤ ((Nat.floor x : ℝ) + 1) - x := by
    linarith
  have hcast : ((Nat.floor x + 1 : ℕ) : ℝ) = (Nat.floor x : ℝ) + 1 := by
    norm_num
  rw [hcast, abs_of_nonneg hnonneg]
  linarith

private lemma terminalKmDepth_six : terminalKmDepth 6 = 9 := by
  unfold terminalKmDepth
  have hlower : (8 : ℝ) ≤ (6 : ℝ) * terminalKmSlope := by
    have hlt : (8 : ℝ) < (6 : ℝ) * terminalKmSlope := by
      nlinarith [four_thirds_lt_terminalKmSlope]
    linarith
  have hupper : (6 : ℝ) * terminalKmSlope < 9 := by
    nlinarith [terminalKmSlope_lt_three_halves]
  have hupper' : (6 : ℝ) * terminalKmSlope < (8 : ℝ) + 1 := by
    linarith
  have hfloor : Nat.floor ((6 : ℝ) * terminalKmSlope) = 8 := by
    refine (Nat.floor_eq_iff ?_).2 ⟨hlower, hupper'⟩
    positivity
  simp [hfloor]

/-- Binary/Fibonacci depth rescaling: the depth index differs from `m log_φ 2` by a bounded
amount, the tail depth differs from `(log_φ 2 - 1)m` by the same bounded amount, and the
window-6 calibration lands at depth `9`. `cor:terminal-Km-depth-rescaling` -/
theorem paper_terminal_km_depth_rescaling :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      |(terminalKmDepth m : ℝ) - (m : ℝ) * terminalKmSlope| ≤ C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      |((terminalKmDepth m : ℝ) - (m : ℝ)) - ((terminalKmSlope - 1) * (m : ℝ))| ≤ C) ∧
    terminalKmDepth 6 = 9 := by
  refine ⟨⟨1, by norm_num, terminalKmDepth_error_le_one⟩, ⟨1, by norm_num, ?_⟩,
    terminalKmDepth_six⟩
  intro m
  have hbase := terminalKmDepth_error_le_one m
  have hrewrite :
      ((terminalKmDepth m : ℝ) - (m : ℝ)) - ((terminalKmSlope - 1) * (m : ℝ))
        = (terminalKmDepth m : ℝ) - (m : ℝ) * terminalKmSlope := by
    ring
  simpa [hrewrite] using hbase

end Omega.GU
