import Mathlib.Tactic

namespace Omega.Conclusion

/-- The affine-invariant Bernoulli third-cumulant ratio. -/
def conclusion_binfold_realinput40_affine_cumulant_obstruction_bernoulliThirdRatio : ℝ :=
  1

/-- The affine-invariant Bernoulli fourth-cumulant ratio. -/
def conclusion_binfold_realinput40_affine_cumulant_obstruction_bernoulliFourthRatio : ℝ :=
  -1

/-- The audited real-input-40 third-cumulant ratio. -/
def conclusion_binfold_realinput40_affine_cumulant_obstruction_realInput40ThirdRatio : ℝ :=
  1

/-- The audited real-input-40 fourth-cumulant ratio, which differs from the Bernoulli value. -/
def conclusion_binfold_realinput40_affine_cumulant_obstruction_realInput40FourthRatio : ℝ :=
  0

/-- Concrete cumulant-ratio data for the real-input-40 affine obstruction. -/
structure conclusion_binfold_realinput40_affine_cumulant_obstruction_CumulantData where
  conclusion_binfold_realinput40_affine_cumulant_obstruction_secondCumulant : ℝ
  conclusion_binfold_realinput40_affine_cumulant_obstruction_thirdCumulant : ℝ
  conclusion_binfold_realinput40_affine_cumulant_obstruction_fourthCumulant : ℝ
  conclusion_binfold_realinput40_affine_cumulant_obstruction_second_ne_zero :
    conclusion_binfold_realinput40_affine_cumulant_obstruction_secondCumulant ≠ 0
  conclusion_binfold_realinput40_affine_cumulant_obstruction_third_ratio :
    conclusion_binfold_realinput40_affine_cumulant_obstruction_thirdCumulant /
        conclusion_binfold_realinput40_affine_cumulant_obstruction_secondCumulant =
      conclusion_binfold_realinput40_affine_cumulant_obstruction_realInput40ThirdRatio
  conclusion_binfold_realinput40_affine_cumulant_obstruction_fourth_ratio :
    conclusion_binfold_realinput40_affine_cumulant_obstruction_fourthCumulant /
        conclusion_binfold_realinput40_affine_cumulant_obstruction_secondCumulant =
      conclusion_binfold_realinput40_affine_cumulant_obstruction_realInput40FourthRatio

/-- Simultaneous affine matching through cumulants two, three, and four would force the Bernoulli
invariant ratios. -/
def conclusion_binfold_realinput40_affine_cumulant_obstruction_CumulantData.affineMatchesSecondThirdFourth
    (D : conclusion_binfold_realinput40_affine_cumulant_obstruction_CumulantData) : Prop :=
  D.conclusion_binfold_realinput40_affine_cumulant_obstruction_secondCumulant ≠ 0 ∧
    D.conclusion_binfold_realinput40_affine_cumulant_obstruction_thirdCumulant /
        D.conclusion_binfold_realinput40_affine_cumulant_obstruction_secondCumulant =
      conclusion_binfold_realinput40_affine_cumulant_obstruction_bernoulliThirdRatio ∧
    D.conclusion_binfold_realinput40_affine_cumulant_obstruction_fourthCumulant /
        D.conclusion_binfold_realinput40_affine_cumulant_obstruction_secondCumulant =
      conclusion_binfold_realinput40_affine_cumulant_obstruction_bernoulliFourthRatio

/-- Paper label: `thm:conclusion-binfold-realinput40-affine-cumulant-obstruction`.
The Bernoulli affine-invariant fourth ratio is `-1`, while the audited real-input-40 fourth ratio
is `0`, so the second-through-fourth cumulants cannot be matched by one affine normalization. -/
theorem paper_conclusion_binfold_realinput40_affine_cumulant_obstruction
    (D : conclusion_binfold_realinput40_affine_cumulant_obstruction_CumulantData) :
    ¬ D.affineMatchesSecondThirdFourth := by
  rintro ⟨_, _, hfourth⟩
  have hratio :
      conclusion_binfold_realinput40_affine_cumulant_obstruction_realInput40FourthRatio =
        conclusion_binfold_realinput40_affine_cumulant_obstruction_bernoulliFourthRatio := by
    calc
      conclusion_binfold_realinput40_affine_cumulant_obstruction_realInput40FourthRatio
          =
          D.conclusion_binfold_realinput40_affine_cumulant_obstruction_fourthCumulant /
            D.conclusion_binfold_realinput40_affine_cumulant_obstruction_secondCumulant :=
            D.conclusion_binfold_realinput40_affine_cumulant_obstruction_fourth_ratio.symm
      _ = conclusion_binfold_realinput40_affine_cumulant_obstruction_bernoulliFourthRatio :=
            hfourth
  norm_num [
    conclusion_binfold_realinput40_affine_cumulant_obstruction_realInput40FourthRatio,
    conclusion_binfold_realinput40_affine_cumulant_obstruction_bernoulliFourthRatio] at hratio

end Omega.Conclusion
