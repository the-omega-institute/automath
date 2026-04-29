import Mathlib.Tactic
import Omega.Conclusion.FoldgaugePiZeroRadiusOddGerm

namespace Omega.Conclusion

noncomputable section

/-- Concrete Ramanujan-machine germ data: a convergence radius and a leading unit. -/
structure conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_Germ where
  conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_radius : ℝ
  conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_leadingCoeff : ℝ

namespace conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_Germ

/-- Positive convergence radius for a Ramanujan-machine hypergeometric germ. -/
def conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_positiveRadius
    (G : conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_Germ) : Prop :=
  0 < G.conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_radius

/-- A local unit is represented by a nonzero leading coefficient. -/
def conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_localUnit
    (G : conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_Germ) : Prop :=
  G.conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_leadingCoeff ≠ 0

end conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_Germ

/-- Positive analytic radius for the odd germ means it does not satisfy the zero-radius theorem. -/
def conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_oddGermPositiveRadius
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data) : Prop :=
  ¬ D.conclusion_foldgauge_pi_zero_radius_odd_germ_zero_radius

/-- A formal conjugacy through local units transports positive radius to the odd germ. -/
def conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_formalConjugacy
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data)
    (G psi h : conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_Germ) :
    Prop :=
  G.conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_positiveRadius →
    psi.conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_localUnit →
      h.conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_localUnit →
        conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_oddGermPositiveRadius D

lemma conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_conjugacy_preserves_positiveRadius
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data)
    (G psi h : conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_Germ)
    (hG : G.conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_positiveRadius)
    (hpsi : psi.conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_localUnit)
    (hh : h.conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_localUnit)
    (hconj : conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_formalConjugacy
      D G psi h) :
    conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_oddGermPositiveRadius D :=
  hconj hG hpsi hh

/-- Paper label:
`thm:conclusion-foldgauge-pi-ramanujan-machine-hypergeometric-obstruction`. -/
theorem paper_conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data)
    (G psi h : conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_Germ)
    (hG : G.conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_positiveRadius)
    (hpsi : psi.conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_localUnit)
    (hh : h.conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_localUnit) :
    ¬ conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_formalConjugacy
      D G psi h := by
  intro hconj
  have hOddPositive :
      conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_oddGermPositiveRadius
        D :=
    conclusion_foldgauge_pi_ramanujan_machine_hypergeometric_obstruction_conjugacy_preserves_positiveRadius
      D G psi h hG hpsi hh hconj
  exact hOddPositive (paper_conclusion_foldgauge_pi_zero_radius_odd_germ D)

end

end Omega.Conclusion
