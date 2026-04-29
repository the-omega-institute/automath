import Omega.Zeta.XiSymqGoldenArSmithClosedForm

namespace Omega.Zeta

/-- Paper label: `prop:xi-O-mod-pi-integer-splitting`. -/
theorem paper_xi_o_mod_pi_integer_splitting (e : ℕ) :
    xi_symq_golden_ar_smith_closed_form_exponents e = (e / 2, (e + 1) / 2) ∧
      5 ^ (xi_symq_golden_ar_smith_closed_form_exponents e).1 *
          5 ^ (xi_symq_golden_ar_smith_closed_form_exponents e).2 =
        5 ^ e := by
  constructor
  · simp [xi_symq_golden_ar_smith_closed_form_exponents]
  · have hsum : e / 2 + (e + 1) / 2 = e := by omega
    rw [xi_symq_golden_ar_smith_closed_form_exponents]
    rw [← pow_add, hsum]

end Omega.Zeta
