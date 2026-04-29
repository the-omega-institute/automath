import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- Concrete high-ambient boundary Gödel adhesion data.  The ambient dimension `dG` bounds the
adhesion defect `dG - gamma` between `0` and `dG / n`; bounded bulk and a positive lower scale are
kept as quantitative hypotheses. -/
structure conclusion_boundary_godel_highambient_adhesion_saturation_data where
  conclusion_boundary_godel_highambient_adhesion_saturation_dG : ℕ → ℝ
  conclusion_boundary_godel_highambient_adhesion_saturation_gamma : ℕ → ℝ
  conclusion_boundary_godel_highambient_adhesion_saturation_dG_pos :
    ∀ n : ℕ, 0 < conclusion_boundary_godel_highambient_adhesion_saturation_dG n
  conclusion_boundary_godel_highambient_adhesion_saturation_gap_nonneg :
    ∀ n : ℕ,
      0 ≤
        conclusion_boundary_godel_highambient_adhesion_saturation_dG n -
          conclusion_boundary_godel_highambient_adhesion_saturation_gamma n
  conclusion_boundary_godel_highambient_adhesion_saturation_gap_upper :
    ∀ n : ℕ,
      conclusion_boundary_godel_highambient_adhesion_saturation_dG n -
          conclusion_boundary_godel_highambient_adhesion_saturation_gamma n ≤
        conclusion_boundary_godel_highambient_adhesion_saturation_dG n / (n : ℝ)
  conclusion_boundary_godel_highambient_adhesion_saturation_bulk_bound :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ n : ℕ, conclusion_boundary_godel_highambient_adhesion_saturation_dG n ≤ C

/-- The adhesion gap tends to zero in high ambient dimension. -/
def conclusion_boundary_godel_highambient_adhesion_saturation_data.adhesionGapTendsToZero
    (D : conclusion_boundary_godel_highambient_adhesion_saturation_data) : Prop :=
  Tendsto
    (fun n : ℕ =>
      D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n -
        D.conclusion_boundary_godel_highambient_adhesion_saturation_gamma n)
    atTop (nhds 0)

/-- The adhesion ratio saturates the ambient boundary dimension. -/
def conclusion_boundary_godel_highambient_adhesion_saturation_data.adhesionRatioTendsToOne
    (D : conclusion_boundary_godel_highambient_adhesion_saturation_data) : Prop :=
  Tendsto
    (fun n : ℕ =>
      D.conclusion_boundary_godel_highambient_adhesion_saturation_gamma n /
        D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n)
    atTop (nhds 1)

/-- Paper label: `thm:conclusion-boundary-godel-highambient-adhesion-saturation`. -/
theorem paper_conclusion_boundary_godel_highambient_adhesion_saturation
    (D : conclusion_boundary_godel_highambient_adhesion_saturation_data) :
    D.adhesionGapTendsToZero ∧ D.adhesionRatioTendsToOne := by
  rcases D.conclusion_boundary_godel_highambient_adhesion_saturation_bulk_bound with
    ⟨C, _hC_nonneg, hC_bound⟩
  have hC_div :
      Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (nhds (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hgap :
      D.adhesionGapTendsToZero := by
    refine squeeze_zero'
      (Eventually.of_forall
        D.conclusion_boundary_godel_highambient_adhesion_saturation_gap_nonneg) ?_ hC_div
    refine Eventually.of_forall fun n => ?_
    calc
      D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n -
          D.conclusion_boundary_godel_highambient_adhesion_saturation_gamma n ≤
          D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n / (n : ℝ) :=
        D.conclusion_boundary_godel_highambient_adhesion_saturation_gap_upper n
      _ ≤ C / (n : ℝ) :=
        div_le_div_of_nonneg_right (hC_bound n) (Nat.cast_nonneg n)
  have hgap_ratio :
      Tendsto
        (fun n : ℕ =>
          (D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n -
              D.conclusion_boundary_godel_highambient_adhesion_saturation_gamma n) /
            D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n)
        atTop (nhds (0 : ℝ)) := by
    refine squeeze_zero' ?_ ?_ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    · exact Eventually.of_forall fun n =>
        div_nonneg
          (D.conclusion_boundary_godel_highambient_adhesion_saturation_gap_nonneg n)
          (le_of_lt (D.conclusion_boundary_godel_highambient_adhesion_saturation_dG_pos n))
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hdG_pos :
          0 < D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n :=
        D.conclusion_boundary_godel_highambient_adhesion_saturation_dG_pos n
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      calc
        (D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n -
              D.conclusion_boundary_godel_highambient_adhesion_saturation_gamma n) /
            D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n ≤
            (D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n / (n : ℝ)) /
              D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n :=
          div_le_div_of_nonneg_right
            (D.conclusion_boundary_godel_highambient_adhesion_saturation_gap_upper n)
            (le_of_lt hdG_pos)
        _ = 1 / (n : ℝ) := by
          field_simp [ne_of_gt hdG_pos, ne_of_gt hn_pos]
  have hratio_eventually :
      (fun n : ℕ =>
          D.conclusion_boundary_godel_highambient_adhesion_saturation_gamma n /
            D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n) =ᶠ[atTop]
        fun n : ℕ =>
          1 -
            (D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n -
                D.conclusion_boundary_godel_highambient_adhesion_saturation_gamma n) /
              D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n := by
    refine Eventually.of_forall fun n => ?_
    have hdG_ne :
        D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n ≠ 0 :=
      ne_of_gt (D.conclusion_boundary_godel_highambient_adhesion_saturation_dG_pos n)
    field_simp [hdG_ne]
    ring
  have hratio :
      D.adhesionRatioTendsToOne := by
    have hsub :
        Tendsto
          (fun n : ℕ =>
            1 -
              (D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n -
                  D.conclusion_boundary_godel_highambient_adhesion_saturation_gamma n) /
                D.conclusion_boundary_godel_highambient_adhesion_saturation_dG n)
          atTop (nhds (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub hgap_ratio)
    exact hsub.congr' hratio_eventually.symm
  exact ⟨hgap, hratio⟩

end Omega.Conclusion
