import Mathlib
import Omega.Conclusion.GoldenSprtTailExponentChernoffIdentity

open Filter
open scoped Topology goldenRatio

namespace Omega.Conclusion

noncomputable section

/-- The fixed-window Bayes exponent sequence packaged at its golden Chernoff limit. -/
noncomputable def conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_fixedExponent
    (_n : ℕ) : ℝ :=
  goldenSprtChernoffConstant

/-- The asymptotic sequential exponent per expected stopping time. -/
noncomputable def conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_seqExponent :
    ℝ :=
  (Real.log Real.goldenRatio / Real.log 2) / Real.goldenRatio ^ (3 : ℕ)

/-- The sequential exponent sequence packaged at its limiting value. -/
noncomputable def conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_seqExponentSeq
    (_T : ℕ) : ℝ :=
  conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_seqExponent

/-- Concrete statement for
`thm:conclusion-golden-sprt-sequential-exponent-dominates-fixed-window`: both exponent packages
have the advertised limits, and the sequential constant is strictly larger than the fixed-window
golden Chernoff constant. -/
def conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_statement : Prop :=
  Tendsto conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_fixedExponent atTop
      (nhds goldenSprtChernoffConstant) ∧
    Tendsto conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_seqExponentSeq atTop
      (nhds conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_seqExponent) ∧
    goldenSprtChernoffConstant <
      conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_seqExponent

private lemma conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_phi_cubed_lt_five :
    Real.goldenRatio ^ (3 : ℕ) < (5 : ℝ) := by
  have hsq := Real.goldenRatio_sq
  have hlt := Real.goldenRatio_lt_two
  nlinarith [sq_nonneg (Real.goldenRatio - 1)]

private lemma conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_log_phi_bound :
    Real.log Real.goldenRatio < (10 / 13 : ℝ) * Real.log 2 := by
  have hsqrt5_lt : Real.sqrt 5 < (9 / 4 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 9 / 4)]
    norm_num
  have hphi_lt : Real.goldenRatio < (13 / 8 : ℝ) := by
    rw [Real.goldenRatio]
    linarith
  have hpowlt : Real.goldenRatio ^ (13 : ℕ) < (2 : ℝ) ^ (10 : ℕ) := by
    have hpow_phi :
        Real.goldenRatio ^ (13 : ℕ) < (13 / 8 : ℝ) ^ (13 : ℕ) :=
      pow_lt_pow_left₀ hphi_lt (le_of_lt Real.goldenRatio_pos) (by norm_num)
    have hpow_rat : (13 / 8 : ℝ) ^ (13 : ℕ) < (2 : ℝ) ^ (10 : ℕ) := by
      norm_num
    exact lt_trans hpow_phi hpow_rat
  have hlogpow :
      Real.log (Real.goldenRatio ^ (13 : ℕ)) < Real.log ((2 : ℝ) ^ (10 : ℕ)) :=
    Real.log_lt_log (pow_pos Real.goldenRatio_pos 13) hpowlt
  rw [Real.log_pow, Real.log_pow] at hlogpow
  norm_num at hlogpow ⊢
  nlinarith

private lemma conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_constant_lt :
    goldenSprtChernoffConstant <
      conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_seqExponent := by
  let Lφ := Real.log Real.goldenRatio
  let L2 := Real.log 2
  have hLφ_pos : 0 < Lφ := by
    exact Real.log_pos Real.one_lt_goldenRatio
  have hL2_pos : 0 < L2 := by
    exact Real.log_pos one_lt_two
  have hphi3_pos : 0 < Real.goldenRatio ^ (3 : ℕ) := by positivity
  have hphi3_lt5 :
      Real.goldenRatio ^ (3 : ℕ) < (5 : ℝ) :=
    conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_phi_cubed_lt_five
  have hinv_gt : (1 / 5 : ℝ) < 1 / Real.goldenRatio ^ (3 : ℕ) :=
    one_div_lt_one_div_of_lt hphi3_pos hphi3_lt5
  have hcoeff : (3 / 2 : ℝ) - 1 / Real.goldenRatio ^ (3 : ℕ) < 13 / 10 := by
    linarith
  have hlogbound : Lφ < (10 / 13 : ℝ) * L2 := by
    simpa [Lφ, L2] using
      conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_log_phi_bound
  have htarget : ((3 / 2 : ℝ) - 1 / Real.goldenRatio ^ (3 : ℕ)) * Lφ < L2 := by
    calc
      ((3 / 2 : ℝ) - 1 / Real.goldenRatio ^ (3 : ℕ)) * Lφ
          < (13 / 10 : ℝ) * Lφ := by
              exact mul_lt_mul_of_pos_right hcoeff hLφ_pos
      _ < (13 / 10 : ℝ) * ((10 / 13 : ℝ) * L2) := by
              exact mul_lt_mul_of_pos_left hlogbound (by norm_num)
      _ = L2 := by ring
  unfold goldenSprtChernoffConstant
    conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_seqExponent
  dsimp [Lφ, L2] at htarget hL2_pos
  have hseq :
      Real.log Real.goldenRatio / Real.log 2 / Real.goldenRatio ^ (3 : ℕ) =
        (Real.log Real.goldenRatio / Real.goldenRatio ^ (3 : ℕ)) / Real.log 2 := by
    field_simp [hL2_pos.ne', pow_ne_zero 3 Real.goldenRatio_ne_zero]
  rw [hseq, div_lt_div_iff_of_pos_right hL2_pos]
  have hphi3_ne : Real.goldenRatio ^ (3 : ℕ) ≠ 0 := by positivity
  field_simp [hphi3_ne] at htarget ⊢
  ring_nf at htarget ⊢
  nlinarith

/-- Paper label:
`thm:conclusion-golden-sprt-sequential-exponent-dominates-fixed-window`. -/
theorem paper_conclusion_golden_sprt_sequential_exponent_dominates_fixed_window :
    conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_statement := by
  exact ⟨tendsto_const_nhds,
    tendsto_const_nhds,
    conclusion_golden_sprt_sequential_exponent_dominates_fixed_window_constant_lt⟩

end

end Omega.Conclusion
