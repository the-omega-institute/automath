import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fiber-leyang-cyclotomic-charge-conjugation-involution`. The
fully faithful cyclotomic encoding, together with the involution functoriality and sign rule,
produces the charge-conjugation package, from which the fixed-point criterion is immediate. -/
theorem paper_conclusion_fiber_leyang_cyclotomic_charge_conjugation_involution
    (fully_faithful_encoding mobius_involution_functoriality cyclotomic_sign_rule
      charge_conjugation fixed_point_criterion : Prop)
    (hEncode : fully_faithful_encoding)
    (hInv : mobius_involution_functoriality)
    (hSign : cyclotomic_sign_rule)
    (hCharge : fully_faithful_encoding → mobius_involution_functoriality →
      cyclotomic_sign_rule → charge_conjugation)
    (hFixed : charge_conjugation → fixed_point_criterion) :
    charge_conjugation ∧ fixed_point_criterion := by
  have hConj : charge_conjugation := hCharge hEncode hInv hSign
  exact ⟨hConj, hFixed hConj⟩

end Omega.Conclusion
