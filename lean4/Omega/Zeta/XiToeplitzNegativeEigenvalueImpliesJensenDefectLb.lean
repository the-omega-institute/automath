import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppJensenSingleZeroLowerBound
import Omega.Zeta.JensenSoftThresholdLowerBound

namespace Omega.Zeta

open Omega.UnitCirclePhaseArithmetic
open Omega.Zeta.JensenSoftThresholdLowerBound

/-- Paper label: `prop:xi-toeplitz-negative-eigenvalue-implies-jensen-defect-lb`.
The Toeplitz-side negative-eigenvalue depth input is encoded by the concrete inequality
`c * η / N ≤ 1 - ‖a‖`, and the conclusion packages the single-zero Jensen lower bound together
with the elementary estimate `-log t ≥ 1 - t`. -/
def xi_toeplitz_negative_eigenvalue_implies_jensen_defect_lb_statement
    (N : ℕ) (η c : ℝ) (a : ℂ) : Prop :=
  0 < N →
    0 < η →
      0 < c →
        0 < ‖a‖ →
          ‖a‖ < 1 →
            c * η / N ≤ 1 - ‖a‖ →
              (∀ ρ : ℝ, ‖a‖ < ρ → ρ < 1 →
                Real.log (ρ / ‖a‖) ≤ appSingleZeroJensenDefect ρ ({a} : Finset ℂ)) ∧
                c * η / N ≤ Real.log (1 / ‖a‖) ∧
                ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ,
                  ‖a‖ < ρ ∧ ρ < 1 ∧
                    c * η / N - ε ≤ appSingleZeroJensenDefect ρ ({a} : Finset ℂ)

theorem paper_xi_toeplitz_negative_eigenvalue_implies_jensen_defect_lb
    (N : ℕ) (η c : ℝ) (a : ℂ) :
    xi_toeplitz_negative_eigenvalue_implies_jensen_defect_lb_statement N η c a := by
  intro hN hη hc ha0 ha1 hdepth
  have hsingle :=
    paper_app_jensen_single_zero_lower_bound ({a} : Finset ℂ) (a := a)
      (by simp) ha0 ha1
  have hlog : 1 - ‖a‖ ≤ Real.log (1 / ‖a‖) := by
    simpa [one_div, inv_inv] using
      (Real.one_sub_inv_le_log_of_pos (x := 1 / ‖a‖) (one_div_pos.mpr ha0))
  have hbound : c * η / N ≤ Real.log (1 / ‖a‖) := le_trans hdepth hlog
  refine ⟨hsingle.1, hbound, ?_⟩
  intro ε hε
  rcases hsingle.2.1 ε hε with ⟨ρ, hρgt, hρlt, hρdefect⟩
  refine ⟨ρ, hρgt, hρlt, ?_⟩
  linarith

end Omega.Zeta
