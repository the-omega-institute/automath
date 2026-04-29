import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppJensenSingleZeroLowerBound
import Omega.UnitCirclePhaseArithmetic.AppRHIffJensenDefectZero

open Filter

namespace Omega.UnitCirclePhaseArithmetic

open Omega.TypedAddressBiaxialCompletion
open JensenCountableCriterionData

/-- Paper label: `thm:app-rh-iff-jensen-defect-vanishing-sequence`.
The chapter-local RH predicate is equivalent to the existence of a monotone radius sequence
approaching the boundary along which the Jensen defect vanishes. The reverse implication uses the
single-zero lower bound: any disk zero forces a positive lower barrier for sufficiently large
radius layers. -/
theorem paper_app_rh_iff_jensen_defect_vanishing_sequence
    (D : JensenCountableCriterionData) (roots : Finset ℂ)
    (hdefect :
      ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 → D.defect ρ = appSingleZeroJensenDefect ρ roots)
    (hdiskZero : ¬ D.rh → ∃ a : ℂ, a ∈ roots ∧ 0 < ‖a‖ ∧ ‖a‖ < 1) :
    D.rh ↔
      ∃ ρseq : ℕ → ℝ,
        Monotone ρseq ∧
          Tendsto ρseq atTop (nhds 1) ∧
            (∀ n : ℕ, 0 < ρseq n ∧ ρseq n < 1) ∧
              (∀ {ρ : ℝ}, 0 < ρ → ρ < 1 → ∃ n : ℕ, ρ ≤ ρseq n) ∧
                Tendsto (fun n : ℕ => D.defect (ρseq n)) atTop (nhds 0) := by
  have hzero := paper_app_rh_iff_jensen_defect_zero D
  constructor
  · intro hRh
    refine ⟨D.rhoSeq, D.rhoSeq_mono, D.rhoSeq_tendsto, D.rhoSeq_mem, D.rhoSeq_covers, ?_⟩
    have hvanish : ∀ n : ℕ, D.defect (D.rhoSeq n) = 0 := by
      intro n
      have hmem := D.rhoSeq_mem n
      exact hzero.mp hRh hmem.1 hmem.2
    refine Tendsto.congr' ?_ tendsto_const_nhds
    exact Filter.Eventually.of_forall (fun n => (hvanish n).symm)
  · rintro ⟨ρseq, hρmono, hρtend, hρmem, hρcovers, hdefect_zero⟩
    by_contra hnotRh
    rcases hdiskZero hnotRh with ⟨a, ha_mem, ha_pos, ha_unit⟩
    have hsingle := paper_app_jensen_single_zero_lower_bound roots ha_mem ha_pos ha_unit
    let ρ0 : ℝ := (‖a‖ + 1) / 2
    have hρ0_pos : 0 < ρ0 := by
      dsimp [ρ0]
      nlinarith
    have hρ0_lt : ρ0 < 1 := by
      dsimp [ρ0]
      nlinarith
    have hρ0_gt : ‖a‖ < ρ0 := by
      dsimp [ρ0]
      nlinarith
    have hlog_pos : 0 < Real.log (ρ0 / ‖a‖) := by
      have hone_lt : 1 < ρ0 / ‖a‖ := (one_lt_div ha_pos).2 hρ0_gt
      exact Real.log_pos hone_lt
    obtain ⟨n0, hn0⟩ := hρcovers hρ0_pos hρ0_lt
    have hsmall : ∀ᶠ n in atTop, D.defect (ρseq n) < Real.log (ρ0 / ‖a‖) := by
      exact hdefect_zero (Iio_mem_nhds hlog_pos)
    obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp hsmall
    let n := max n0 N
    have hn0_le : n0 ≤ n := le_max_left _ _
    have hN_le : N ≤ n := le_max_right _ _
    have hρn_mem := hρmem n
    have hρ0_le : ρ0 ≤ ρseq n := by
      calc
        ρ0 ≤ ρseq n0 := hn0
        _ ≤ ρseq n := hρmono hn0_le
    have hρn_gt : ‖a‖ < ρseq n := lt_of_lt_of_le hρ0_gt hρ0_le
    have hLower :
        Real.log (ρ0 / ‖a‖) ≤ D.defect (ρseq n) := by
      calc
        Real.log (ρ0 / ‖a‖) ≤ Real.log (ρseq n / ‖a‖) := by
          have hdiv :
              ρ0 / ‖a‖ ≤ ρseq n / ‖a‖ := by
            exact div_le_div_of_nonneg_right hρ0_le ha_pos.le
          exact Real.log_le_log (by positivity) hdiv
        _ ≤ appSingleZeroJensenDefect (ρseq n) roots := hsingle.1 (ρseq n) hρn_gt hρn_mem.2
        _ = D.defect (ρseq n) := by
          symm
          exact hdefect hρn_mem.1 hρn_mem.2
    have hUpper : D.defect (ρseq n) < Real.log (ρ0 / ‖a‖) := hN n hN_le
    exact (not_lt_of_ge hLower) hUpper

end Omega.UnitCirclePhaseArithmetic
