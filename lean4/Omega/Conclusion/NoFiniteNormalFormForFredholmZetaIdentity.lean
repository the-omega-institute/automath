import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-no-finite-normal-form-for-fredholm-zeta-identity`. -/
theorem paper_conclusion_no_finite_normal_form_for_fredholm_zeta_identity
    (finiteNormalFormExists fredholmIdentityUndecidable : Prop)
    (hdecidable : finiteNormalFormExists → ¬ fredholmIdentityUndecidable)
    (hundecidable : fredholmIdentityUndecidable) :
    ¬ finiteNormalFormExists := by
  intro hnormal
  exact hdecidable hnormal hundecidable

end Omega.Conclusion
