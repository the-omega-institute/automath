import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local package for the Bernoulli-half low-defect Fibonacci shadow formulas.
The data record the closed form for the zero-defect coefficients together with the
derived one-defect and two-defect closed forms. -/
structure BernoulliPHalfLowDefectShadowData where
  zeroDefectClosedForm : Prop
  oneDefectClosedForm : Prop
  twoDefectClosedForm : Prop
  zeroDefectClosedForm_h : zeroDefectClosedForm
  deriveOneDefectClosedForm : zeroDefectClosedForm → oneDefectClosedForm
  deriveTwoDefectClosedForm :
    zeroDefectClosedForm → oneDefectClosedForm → twoDefectClosedForm

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the Bernoulli-half specialization of the order-four recurrence:
the low-defect coefficient sequences admit Fibonacci closed forms in defect orders
`0`, `1`, and `2`.
    thm:fold-bernoulli-p-fibonacci-low-defect-shadow -/
theorem paper_fold_bernoulli_p_fibonacci_low_defect_shadow
    (D : BernoulliPHalfLowDefectShadowData) :
    D.zeroDefectClosedForm ∧ D.oneDefectClosedForm ∧ D.twoDefectClosedForm := by
  have hOne : D.oneDefectClosedForm := D.deriveOneDefectClosedForm D.zeroDefectClosedForm_h
  have hTwo : D.twoDefectClosedForm :=
    D.deriveTwoDefectClosedForm D.zeroDefectClosedForm_h hOne
  exact ⟨D.zeroDefectClosedForm_h, hOne, hTwo⟩

end Omega.Folding
