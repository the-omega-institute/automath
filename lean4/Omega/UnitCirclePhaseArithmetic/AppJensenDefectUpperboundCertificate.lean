import Mathlib.Analysis.SpecificLimits.Basic
import Omega.UnitCirclePhaseArithmetic.AppRHIffJensenDefectVanishingSequence

open Filter

namespace Omega.UnitCirclePhaseArithmetic

open Omega.TypedAddressBiaxialCompletion
open JensenCountableCriterionData

/-- Paper label: `cor:app-jensen-defect-upperbound-certificate`.
A monotone radius sequence approaching `1` together with an antitone upper envelope
`εₙ ↓ 0` forces the Jensen defect to vanish along the sequence, so the existing vanishing-sequence
criterion rules out every disk zero and yields RH. -/
theorem paper_app_jensen_defect_upperbound_certificate
    (D : JensenCountableCriterionData) (roots : Finset ℂ)
    (hdefect :
      ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 → D.defect ρ = appSingleZeroJensenDefect ρ roots)
    (hupper :
      ∃ ρseq εseq : ℕ → ℝ,
        Monotone ρseq ∧
          Tendsto ρseq atTop (nhds 1) ∧
            Antitone εseq ∧
              Tendsto εseq atTop (nhds 0) ∧
                (∀ n : ℕ, 0 < ρseq n ∧ ρseq n < 1 ∧ 0 ≤ εseq n) ∧
                  (∀ n : ℕ, D.defect (ρseq n) ≤ εseq n)) :
    D.rh := by
  rcases hupper with ⟨ρseq, εseq, hρmono, hρtend, _hεanti, hεtend, hmem, hupperBound⟩
  have hdefect_tendsto :
      Tendsto (fun n : ℕ => D.defect (ρseq n)) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεtend ?_ ?_
    · intro n
      exact (D.semantics (ρseq n) (hmem n).1 (hmem n).2.1).1
    · intro n
      exact hupperBound n
  have hρcovers : ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 → ∃ n : ℕ, ρ ≤ ρseq n := by
    intro ρ hρ0 hρ1
    have hlarge : ∀ᶠ n : ℕ in atTop, ρ < ρseq n := hρtend (Ioi_mem_nhds hρ1)
    obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp hlarge
    exact ⟨N, le_of_lt (hN N le_rfl)⟩
  have hdiskZero : ¬ D.rh → ∃ a : ℂ, a ∈ roots ∧ 0 < ‖a‖ ∧ ‖a‖ < 1 := by
    intro hnotRh
    by_contra hnoZero
    apply hnotRh
    intro ρ hρ0 hρ1
    have hdef_eq : D.defect ρ = appSingleZeroJensenDefect ρ roots := hdefect hρ0 hρ1
    have hallOutside :
        ∀ a : ℂ, a ∈ roots → ‖a‖ = 0 ∨ 1 ≤ ‖a‖ := by
      intro a ha
      by_cases hnorm0 : ‖a‖ = 0
      · exact Or.inl hnorm0
      · right
        by_contra ha_bad
        have hpos : 0 < ‖a‖ := by
          exact lt_of_le_of_ne (norm_nonneg a) (by simpa [eq_comm] using hnorm0)
        have hlt : ‖a‖ < 1 := by linarith
        exact hnoZero ⟨a, ha, hpos, hlt⟩
    have hterm_zero :
        ∀ a ∈ roots, max (Real.log (ρ / ‖a‖)) 0 = 0 := by
      intro a ha
      rcases hallOutside a ha with ha_zero | ha_outside
      · have hρ_div_zero : ρ / ‖a‖ = 0 := by simp [ha_zero]
        simp [ha_zero]
      · have hdiv_le_one : ρ / ‖a‖ ≤ 1 := by
          have hρ_le_norm : ρ ≤ ‖a‖ := by linarith
          have hnorm_pos : 0 < ‖a‖ := by linarith
          have hnorm_ne : ‖a‖ ≠ 0 := ne_of_gt hnorm_pos
          field_simp [hnorm_ne]
          linarith
        have hlog_nonpos : Real.log (ρ / ‖a‖) ≤ 0 := by
          have hdiv_nonneg : 0 ≤ ρ / ‖a‖ := by positivity
          exact Real.log_nonpos hdiv_nonneg hdiv_le_one
        exact max_eq_right hlog_nonpos
    have happ_zero : appSingleZeroJensenDefect ρ roots = 0 := by
      unfold appSingleZeroJensenDefect
      refine Finset.sum_eq_zero ?_
      intro a ha
      exact hterm_zero a ha
    exact (D.semantics ρ hρ0 hρ1).2.mp (hdef_eq.trans happ_zero)
  intro ρ hρ0 hρ1
  exact
    ((paper_app_rh_iff_jensen_defect_vanishing_sequence D roots hdefect hdiskZero).2
      ⟨ρseq, hρmono, hρtend, fun n => ⟨(hmem n).1, (hmem n).2.1⟩,
        fun {ρ} hρ0 hρ1 => hρcovers hρ0 hρ1, hdefect_tendsto⟩) hρ0 hρ1

end Omega.UnitCirclePhaseArithmetic
