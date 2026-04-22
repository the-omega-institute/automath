import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.BinfoldEscortCsiszarBlackwellPhi
import Omega.Conclusion.PowerDivergenceSecondorderRecurrence

namespace Omega.Conclusion

noncomputable section

/-- Concrete wrapper for recovering the golden constants and the full power-divergence family from
the single `χ²` baseline constant. -/
structure conclusion_chi2_recovers_full_power_divergence_family_data where
  conclusion_chi2_recovers_full_power_divergence_family_witness : Unit := ()

/-- The distinguished `χ²` baseline constant from the binary escort package. -/
noncomputable def conclusion_chi2_recovers_full_power_divergence_family_chi2_constant : ℝ :=
  BinfoldEscortCsiszarBlackwellPhiDatum.chi2UniformBaseline

/-- The concrete two-exponential family used in the power-divergence recurrence package. -/
noncomputable def conclusion_chi2_recovers_full_power_divergence_family_power_divergence_data :
    PowerDivergenceSpectrumData :=
  { leftWeight := (Real.goldenRatio⁻¹) ^ 2
    rightWeight := Real.goldenRatio⁻¹
    leftRate := Real.log (Real.goldenRatio / Real.sqrt 5)
    rightRate := Real.log (Real.goldenRatio ^ 2 / Real.sqrt 5)
    hleftWeight := by positivity
    hrightWeight := by positivity
    hrate := by
      have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
      have hlt : Real.goldenRatio / Real.sqrt 5 < Real.goldenRatio ^ 2 / Real.sqrt 5 := by
        have hphi : Real.goldenRatio < Real.goldenRatio ^ 2 := by
          nlinarith [Real.goldenRatio_sq]
        exact (div_lt_div_iff_of_pos_right hsqrt5_pos).2 hphi
      exact Real.log_lt_log (by positivity) hlt }

namespace conclusion_chi2_recovers_full_power_divergence_family_data

/-- The displayed `χ²` constant recovers `√5`. -/
def conclusion_chi2_recovers_full_power_divergence_family_sqrt5_recovered
    (_D : conclusion_chi2_recovers_full_power_divergence_family_data) : Prop :=
  Real.sqrt 5 = 5 * conclusion_chi2_recovers_full_power_divergence_family_chi2_constant + 2

/-- The displayed `χ²` constant recovers `φ`. -/
def conclusion_chi2_recovers_full_power_divergence_family_phi_recovered
    (_D : conclusion_chi2_recovers_full_power_divergence_family_data) : Prop :=
  Real.goldenRatio =
    (5 * conclusion_chi2_recovers_full_power_divergence_family_chi2_constant + 3) / 2

/-- Substituting the recovered constants into the explicit two-exponential formula yields the full
power-divergence family. -/
def conclusion_chi2_recovers_full_power_divergence_family_full_family_recovered
    (_D : conclusion_chi2_recovers_full_power_divergence_family_data) : Prop :=
  ∀ n : ℕ,
    conclusion_chi2_recovers_full_power_divergence_family_power_divergence_data.spectrum n =
      conclusion_chi2_recovers_full_power_divergence_family_power_divergence_data.leftWeight *
          Real.exp
            (Real.log
                (((5 * conclusion_chi2_recovers_full_power_divergence_family_chi2_constant + 3) /
                    2) /
                  (5 * conclusion_chi2_recovers_full_power_divergence_family_chi2_constant + 2)) *
              n) +
        conclusion_chi2_recovers_full_power_divergence_family_power_divergence_data.rightWeight *
          Real.exp
            (Real.log
                ((((5 * conclusion_chi2_recovers_full_power_divergence_family_chi2_constant + 3) /
                        2) ^
                      2) /
                  (5 * conclusion_chi2_recovers_full_power_divergence_family_chi2_constant + 2)) *
              n)

end conclusion_chi2_recovers_full_power_divergence_family_data

private theorem conclusion_chi2_recovers_full_power_divergence_family_phi_formula :
    Real.goldenRatio =
      (5 * conclusion_chi2_recovers_full_power_divergence_family_chi2_constant + 3) / 2 := by
  let D : BinfoldEscortCsiszarBlackwellPhiDatum := { p := 0, q := 1 }
  rcases paper_conclusion_binfold_escort_csiszar_blackwell_phi D with ⟨_, _, _, _, hphi⟩
  simpa [conclusion_chi2_recovers_full_power_divergence_family_chi2_constant] using hphi

private theorem conclusion_chi2_recovers_full_power_divergence_family_sqrt5_formula :
    Real.sqrt 5 = 5 * conclusion_chi2_recovers_full_power_divergence_family_chi2_constant + 2 := by
  have hphi := conclusion_chi2_recovers_full_power_divergence_family_phi_formula
  have hsqrt5_eq : Real.sqrt 5 = 2 * Real.goldenRatio - 1 := by
    have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    have hsqrt5_nonneg : 0 ≤ (Real.sqrt 5 : ℝ) := by positivity
    rw [Real.goldenRatio]
    nlinarith [hsqrt5_sq, hsqrt5_nonneg]
  calc
    Real.sqrt 5 = 2 * Real.goldenRatio - 1 := hsqrt5_eq
    _ = 5 * conclusion_chi2_recovers_full_power_divergence_family_chi2_constant + 2 := by
      rw [hphi]
      ring

/-- Paper label: `cor:conclusion-chi2-recovers-full-power-divergence-family`. -/
theorem paper_conclusion_chi2_recovers_full_power_divergence_family
    (D : conclusion_chi2_recovers_full_power_divergence_family_data) :
    D.conclusion_chi2_recovers_full_power_divergence_family_sqrt5_recovered ∧
      D.conclusion_chi2_recovers_full_power_divergence_family_phi_recovered ∧
      D.conclusion_chi2_recovers_full_power_divergence_family_full_family_recovered := by
  refine ⟨conclusion_chi2_recovers_full_power_divergence_family_sqrt5_formula,
    conclusion_chi2_recovers_full_power_divergence_family_phi_formula, ?_⟩
  intro n
  have hfamily :=
    (paper_conclusion_power_divergence_secondorder_recurrence
      conclusion_chi2_recovers_full_power_divergence_family_power_divergence_data).1 n
  simpa [conclusion_chi2_recovers_full_power_divergence_family_power_divergence_data,
    conclusion_chi2_recovers_full_power_divergence_family_phi_formula,
    conclusion_chi2_recovers_full_power_divergence_family_sqrt5_formula] using hfamily

end

end Omega.Conclusion
