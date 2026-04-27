import Mathlib.Tactic
import Omega.Conclusion.FoldgaugePiZeroRadiusOddGerm

namespace Omega.Conclusion

noncomputable section

/-- Concrete germ data used by the local analytic obstruction: a radius and a leading unit. -/
structure conclusion_foldgauge_pi_borwein_local_analytic_obstruction_Germ where
  conclusion_foldgauge_pi_borwein_local_analytic_obstruction_radius : ℝ
  conclusion_foldgauge_pi_borwein_local_analytic_obstruction_leadingCoeff : ℝ

namespace conclusion_foldgauge_pi_borwein_local_analytic_obstruction_Germ

/-- Positive convergence radius for the Borwein local analytic germ. -/
def conclusion_foldgauge_pi_borwein_local_analytic_obstruction_positiveRadius
    (F : conclusion_foldgauge_pi_borwein_local_analytic_obstruction_Germ) : Prop :=
  0 < F.conclusion_foldgauge_pi_borwein_local_analytic_obstruction_radius

/-- Local units are represented by nonzero leading coefficient. -/
def conclusion_foldgauge_pi_borwein_local_analytic_obstruction_localUnit
    (F : conclusion_foldgauge_pi_borwein_local_analytic_obstruction_Germ) : Prop :=
  F.conclusion_foldgauge_pi_borwein_local_analytic_obstruction_leadingCoeff ≠ 0

end conclusion_foldgauge_pi_borwein_local_analytic_obstruction_Germ

/-- Positive analytic radius for the concrete odd germ means it does not have zero radius. -/
def conclusion_foldgauge_pi_borwein_local_analytic_obstruction_oddGermPositiveRadius
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data) : Prop :=
  ¬ D.conclusion_foldgauge_pi_zero_radius_odd_germ_zero_radius

/-- A formal conjugacy through local units transports positive radius to the odd germ. -/
def conclusion_foldgauge_pi_borwein_local_analytic_obstruction_formalConjugacy
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data)
    (F ψ h : conclusion_foldgauge_pi_borwein_local_analytic_obstruction_Germ) : Prop :=
  F.conclusion_foldgauge_pi_borwein_local_analytic_obstruction_positiveRadius →
    ψ.conclusion_foldgauge_pi_borwein_local_analytic_obstruction_localUnit →
      h.conclusion_foldgauge_pi_borwein_local_analytic_obstruction_localUnit →
        conclusion_foldgauge_pi_borwein_local_analytic_obstruction_oddGermPositiveRadius D

lemma conclusion_foldgauge_pi_borwein_local_analytic_obstruction_conjugacy_preserves_positiveRadius
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data)
    (F ψ h : conclusion_foldgauge_pi_borwein_local_analytic_obstruction_Germ)
    (hF : F.conclusion_foldgauge_pi_borwein_local_analytic_obstruction_positiveRadius)
    (hψ : ψ.conclusion_foldgauge_pi_borwein_local_analytic_obstruction_localUnit)
    (hh : h.conclusion_foldgauge_pi_borwein_local_analytic_obstruction_localUnit)
    (hconj : conclusion_foldgauge_pi_borwein_local_analytic_obstruction_formalConjugacy
      D F ψ h) :
    conclusion_foldgauge_pi_borwein_local_analytic_obstruction_oddGermPositiveRadius D := by
  exact hconj hF hψ hh

/-- Paper label: `thm:conclusion-foldgauge-pi-borwein-local-analytic-obstruction`. -/
theorem paper_conclusion_foldgauge_pi_borwein_local_analytic_obstruction
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data)
    (F ψ h : conclusion_foldgauge_pi_borwein_local_analytic_obstruction_Germ)
    (hF : F.conclusion_foldgauge_pi_borwein_local_analytic_obstruction_positiveRadius)
    (hψ : ψ.conclusion_foldgauge_pi_borwein_local_analytic_obstruction_localUnit)
    (hh : h.conclusion_foldgauge_pi_borwein_local_analytic_obstruction_localUnit) :
    ¬ conclusion_foldgauge_pi_borwein_local_analytic_obstruction_formalConjugacy D F ψ h := by
  intro hconj
  have hDpos :
      conclusion_foldgauge_pi_borwein_local_analytic_obstruction_oddGermPositiveRadius D :=
    conclusion_foldgauge_pi_borwein_local_analytic_obstruction_conjugacy_preserves_positiveRadius
      D F ψ h hF hψ hh hconj
  exact hDpos (paper_conclusion_foldgauge_pi_zero_radius_odd_germ D)

end

end Omega.Conclusion
