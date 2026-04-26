import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The Jensen defect at radius `ρ` for a finite set of disk zeros. -/
def appSingleZeroJensenDefect (ρ : ℝ) (roots : Finset ℂ) : ℝ :=
  Finset.sum roots (fun z => max (Real.log (ρ / ‖z‖)) 0)

/-- Paper label: `prop:app-jensen-single-zero-lower-bound`.
One zero inside the disk already contributes the Jensen summand `log (ρ / ‖a‖)` to the full
defect, and by choosing `ρ` close to `1` that contribution stays uniformly positive. -/
theorem paper_app_jensen_single_zero_lower_bound
    (roots : Finset ℂ) {a : ℂ} (ha_mem : a ∈ roots) (ha_pos : 0 < ‖a‖) (ha_unit : ‖a‖ < 1) :
    (∀ ρ : ℝ, ‖a‖ < ρ → ρ < 1 → Real.log (ρ / ‖a‖) ≤ appSingleZeroJensenDefect ρ roots) ∧
      (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, ‖a‖ < ρ ∧ ρ < 1 ∧
        Real.log (1 / ‖a‖) - ε ≤ appSingleZeroJensenDefect ρ roots) ∧
      0 < Real.log (1 / ‖a‖) := by
  have hlower :
      ∀ ρ : ℝ, ‖a‖ < ρ → ρ < 1 → Real.log (ρ / ‖a‖) ≤ appSingleZeroJensenDefect ρ roots := by
    intro ρ hρ_gt hρ_lt
    have hlog_nonneg : 0 ≤ Real.log (ρ / ‖a‖) := by
      have hone_le : 1 ≤ ρ / ‖a‖ := by
        have hone_lt : 1 < ρ / ‖a‖ := (one_lt_div ha_pos).2 hρ_gt
        linarith
      exact Real.log_nonneg hone_le
    calc
      Real.log (ρ / ‖a‖) = max (Real.log (ρ / ‖a‖)) 0 := by
        symm
        exact max_eq_left hlog_nonneg
      _ ≤ appSingleZeroJensenDefect ρ roots := by
        unfold appSingleZeroJensenDefect
        rw [Finset.sum_eq_add_sum_diff_singleton ha_mem]
        have hrest_nonneg :
            0 ≤ Finset.sum (roots \ {a}) (fun z => max (Real.log (ρ / ‖z‖)) 0) := by
          refine Finset.sum_nonneg ?_
          intro z hz
          exact le_max_right _ _
        simpa using
          (le_add_of_nonneg_right hrest_nonneg :
            max (Real.log (ρ / ‖a‖)) 0 ≤
              max (Real.log (ρ / ‖a‖)) 0 +
                Finset.sum (roots \ {a}) (fun z => max (Real.log (ρ / ‖z‖)) 0))
  have hlog_pos : 0 < Real.log (1 / ‖a‖) := by
    have hone_lt : 1 < 1 / ‖a‖ := (one_lt_div ha_pos).2 ha_unit
    exact Real.log_pos hone_lt
  refine ⟨hlower, ?_, hlog_pos⟩
  intro ε hε
  let ρ : ℝ := max ((‖a‖ + 1) / 2) (Real.exp (-ε))
  have hρ_gt : ‖a‖ < ρ := by
    have hhalf : ‖a‖ < (‖a‖ + 1) / 2 := by
      nlinarith
    exact hhalf.trans_le (le_max_left _ _)
  have hρ_lt : ρ < 1 := by
    have hleft : (‖a‖ + 1) / 2 < 1 := by
      nlinarith
    have hright : Real.exp (-ε) < 1 := by
      simpa using (Real.exp_lt_one_iff.mpr (by linarith : -ε < 0))
    exact max_lt_iff.mpr ⟨hleft, hright⟩
  have hbound : Real.exp (-ε) ≤ ρ := le_max_right _ _
  have hmain : Real.log (1 / ‖a‖) - ε ≤ Real.log (ρ / ‖a‖) := by
    have hdiv :
        Real.exp (-ε) / ‖a‖ ≤ ρ / ‖a‖ := by
      exact div_le_div_of_nonneg_right hbound ha_pos.le
    have hlog :
        Real.log (Real.exp (-ε) / ‖a‖) ≤ Real.log (ρ / ‖a‖) := by
      exact Real.log_le_log (by positivity) hdiv
    have hleft :
        Real.log (Real.exp (-ε) / ‖a‖) = Real.log (1 / ‖a‖) - ε := by
      rw [Real.log_div (by positivity) (ne_of_gt ha_pos), Real.log_exp]
      rw [one_div, Real.log_inv]
      ring
    exact hleft ▸ hlog
  exact ⟨ρ, hρ_gt, hρ_lt, le_trans hmain (hlower ρ hρ_gt hρ_lt)⟩

end

end Omega.UnitCirclePhaseArithmetic
