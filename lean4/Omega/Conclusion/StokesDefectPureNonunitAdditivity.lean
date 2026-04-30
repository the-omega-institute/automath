import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete rational-rank data for pure nonunit Stokes-defect additivity. The three quotient
rank formulae identify the Stokes defects with nonunit quotient ranks, and the weighted-dimension
formulae identify the visible ranks after amalgamation along the shared unit-free part. -/
structure conclusion_stokes_defect_pure_nonunit_additivity_data where
  conclusion_stokes_defect_pure_nonunit_additivity_u_vis : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_u_vis₁ : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_u_vis₂ : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_delta_St : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_delta_St₁ : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_delta_St₂ : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_wdim : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_wdim₁ : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_wdim₂ : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_unitFreeRank : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_quotientRank : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_quotientRank₁ : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_quotientRank₂ : ℚ
  conclusion_stokes_defect_pure_nonunit_additivity_delta_formula :
    conclusion_stokes_defect_pure_nonunit_additivity_delta_St =
      conclusion_stokes_defect_pure_nonunit_additivity_quotientRank
  conclusion_stokes_defect_pure_nonunit_additivity_delta_formula₁ :
    conclusion_stokes_defect_pure_nonunit_additivity_delta_St₁ =
      conclusion_stokes_defect_pure_nonunit_additivity_quotientRank₁
  conclusion_stokes_defect_pure_nonunit_additivity_delta_formula₂ :
    conclusion_stokes_defect_pure_nonunit_additivity_delta_St₂ =
      conclusion_stokes_defect_pure_nonunit_additivity_quotientRank₂
  conclusion_stokes_defect_pure_nonunit_additivity_quotient_rank_add :
    conclusion_stokes_defect_pure_nonunit_additivity_quotientRank =
      conclusion_stokes_defect_pure_nonunit_additivity_quotientRank₁ +
        conclusion_stokes_defect_pure_nonunit_additivity_quotientRank₂
  conclusion_stokes_defect_pure_nonunit_additivity_wdim_formula :
    conclusion_stokes_defect_pure_nonunit_additivity_wdim =
      conclusion_stokes_defect_pure_nonunit_additivity_u_vis +
        conclusion_stokes_defect_pure_nonunit_additivity_delta_St / 2
  conclusion_stokes_defect_pure_nonunit_additivity_wdim_formula₁ :
    conclusion_stokes_defect_pure_nonunit_additivity_wdim₁ =
      conclusion_stokes_defect_pure_nonunit_additivity_u_vis₁ +
        conclusion_stokes_defect_pure_nonunit_additivity_delta_St₁ / 2
  conclusion_stokes_defect_pure_nonunit_additivity_wdim_formula₂ :
    conclusion_stokes_defect_pure_nonunit_additivity_wdim₂ =
      conclusion_stokes_defect_pure_nonunit_additivity_u_vis₂ +
        conclusion_stokes_defect_pure_nonunit_additivity_delta_St₂ / 2
  conclusion_stokes_defect_pure_nonunit_additivity_wdim_amalgamation :
    conclusion_stokes_defect_pure_nonunit_additivity_wdim =
      conclusion_stokes_defect_pure_nonunit_additivity_wdim₁ +
        conclusion_stokes_defect_pure_nonunit_additivity_wdim₂ -
          conclusion_stokes_defect_pure_nonunit_additivity_unitFreeRank

/-- The Stokes defect is additive on the nonunit quotient, and the visible rank has exactly the
unit-free amalgamation loss. -/
def conclusion_stokes_defect_pure_nonunit_additivity_statement
    (D : conclusion_stokes_defect_pure_nonunit_additivity_data) : Prop :=
  D.conclusion_stokes_defect_pure_nonunit_additivity_delta_St =
      D.conclusion_stokes_defect_pure_nonunit_additivity_delta_St₁ +
        D.conclusion_stokes_defect_pure_nonunit_additivity_delta_St₂ ∧
    D.conclusion_stokes_defect_pure_nonunit_additivity_u_vis =
      D.conclusion_stokes_defect_pure_nonunit_additivity_u_vis₁ +
        D.conclusion_stokes_defect_pure_nonunit_additivity_u_vis₂ -
          D.conclusion_stokes_defect_pure_nonunit_additivity_unitFreeRank

/-- Paper label: `thm:conclusion-stokes-defect-pure-nonunit-additivity`. -/
theorem paper_conclusion_stokes_defect_pure_nonunit_additivity
    (D : conclusion_stokes_defect_pure_nonunit_additivity_data) :
    conclusion_stokes_defect_pure_nonunit_additivity_statement D := by
  unfold conclusion_stokes_defect_pure_nonunit_additivity_statement
  have hdelta :
      D.conclusion_stokes_defect_pure_nonunit_additivity_delta_St =
        D.conclusion_stokes_defect_pure_nonunit_additivity_delta_St₁ +
          D.conclusion_stokes_defect_pure_nonunit_additivity_delta_St₂ := by
    rw [D.conclusion_stokes_defect_pure_nonunit_additivity_delta_formula,
      D.conclusion_stokes_defect_pure_nonunit_additivity_delta_formula₁,
      D.conclusion_stokes_defect_pure_nonunit_additivity_delta_formula₂,
      D.conclusion_stokes_defect_pure_nonunit_additivity_quotient_rank_add]
  refine ⟨hdelta, ?_⟩
  linarith [
    D.conclusion_stokes_defect_pure_nonunit_additivity_wdim_formula,
    D.conclusion_stokes_defect_pure_nonunit_additivity_wdim_formula₁,
    D.conclusion_stokes_defect_pure_nonunit_additivity_wdim_formula₂,
    D.conclusion_stokes_defect_pure_nonunit_additivity_wdim_amalgamation,
    hdelta]

end Omega.Conclusion
