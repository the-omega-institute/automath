import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-cauchy-convolution-denominator-gcd-law`. This abstract wrapper records
the reduced-denominator formula and the cross-coprime cancellation specialization. -/
theorem paper_xi_cauchy_convolution_denominator_gcd_law
    {Den : Type*}
    (mul div gcd : Den → Den → Den)
    (one Va Vb Ua Ub Vc : Den)
    (coprime : Den → Den → Prop)
    (denominatorFormula :
      Vc = div (mul Va Vb) (mul (gcd Va Ub) (gcd Vb Ua)))
    (crossCoprimeCancels :
      coprime Va Ub → coprime Vb Ua → gcd Va Ub = one ∧ gcd Vb Ua = one) :
    Vc = div (mul Va Vb) (mul (gcd Va Ub) (gcd Vb Ua)) ∧
      (coprime Va Ub → coprime Vb Ua → gcd Va Ub = one ∧ gcd Vb Ua = one) := by
  exact ⟨denominatorFormula, crossCoprimeCancels⟩

end Omega.Zeta
