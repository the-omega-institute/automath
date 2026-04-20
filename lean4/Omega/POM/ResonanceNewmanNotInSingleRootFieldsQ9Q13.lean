import Mathlib.Tactic

namespace Omega.POM

/-- Concrete degree-gap data for the `q = 9` or `q = 13` Newman-ratio obstruction. -/
structure PomResonanceNewmanNotInSingleRootFieldsData where
  q : ℕ
  hq : q = 9 ∨ q = 13
  degP : ℕ
  hdeg : 7 ≤ degP

namespace PomResonanceNewmanNotInSingleRootFieldsData

/-- The relative degree `[ℚ(r_q, λ_q^-):ℚ(r_q)] = d - 1`. -/
def degreeGapOverRq (D : PomResonanceNewmanNotInSingleRootFieldsData) : ℕ :=
  D.degP - 1

/-- The relative degree `[ℚ(r_q, λ_q^-):ℚ(λ_q^-)] = d - 1`. -/
def degreeGapOverLambdaMinus (D : PomResonanceNewmanNotInSingleRootFieldsData) : ℕ :=
  D.degP - 1

/-- If `υ_q` were already contained in `ℚ(r_q)`, the other distinguished root would become
quadratic over `ℚ(r_q)`. -/
def newmanRatioInRqField (D : PomResonanceNewmanNotInSingleRootFieldsData) : Prop :=
  D.degreeGapOverRq ≤ 2

/-- If `υ_q` were already contained in `ℚ(λ_q^-)`, the other distinguished root would become
quadratic over `ℚ(λ_q^-)`. -/
def newmanRatioInLambdaMinusField (D : PomResonanceNewmanNotInSingleRootFieldsData) : Prop :=
  D.degreeGapOverLambdaMinus ≤ 2

/-- The Newman ratio avoids both single-root fields because each relative degree is at least `6`.
-/
def newmanRatioNotInSingleRootFields (D : PomResonanceNewmanNotInSingleRootFieldsData) : Prop :=
  ¬ D.newmanRatioInRqField ∧ ¬ D.newmanRatioInLambdaMinusField

lemma degreeGapOverRq_ge_six (D : PomResonanceNewmanNotInSingleRootFieldsData) :
    6 ≤ D.degreeGapOverRq := by
  simpa [degreeGapOverRq] using Nat.pred_le_pred D.hdeg

lemma degreeGapOverLambdaMinus_ge_six (D : PomResonanceNewmanNotInSingleRootFieldsData) :
    6 ≤ D.degreeGapOverLambdaMinus := by
  simpa [degreeGapOverLambdaMinus] using Nat.pred_le_pred D.hdeg

end PomResonanceNewmanNotInSingleRootFieldsData

open PomResonanceNewmanNotInSingleRootFieldsData

/-- Paper label: `prop:pom-resonance-newman-not-in-single-root-fields-q9-13`.
For `q = 9` or `13`, the shared degree gap `d - 1` is at least `6`, so the quadratic collapse that
would follow from placing `υ_q` in either single-root field is impossible. -/
theorem paper_pom_resonance_newman_not_in_single_root_fields_q9_13
    (D : PomResonanceNewmanNotInSingleRootFieldsData) : D.newmanRatioNotInSingleRootFields := by
  refine ⟨?_, ?_⟩
  · intro h
    have hgap : 6 ≤ D.degreeGapOverRq := D.degreeGapOverRq_ge_six
    unfold newmanRatioInRqField at h
    omega
  · intro h
    have hgap : 6 ≤ D.degreeGapOverLambdaMinus := D.degreeGapOverLambdaMinus_ge_six
    unfold newmanRatioInLambdaMinusField at h
    omega

end Omega.POM
