import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-primorial-bodycode-doublelog-beta-parametrization`. The
closed-form pole location and residue are the two projections of the double-log parameterization. -/
theorem paper_conclusion_primorial_bodycode_doublelog_beta_parametrization (n d beta : ℝ) :
    let sStar := n - d
    let residue := Real.exp beta / (d * (Real.log 2) ^ 2)
    sStar = n - d ∧ residue = Real.exp beta / (d * (Real.log 2) ^ 2) := by
  simp

end Omega.Conclusion
