import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Zeta

noncomputable def xi_time_part9xc_serrin_geometry_all_cumulants_vanish_pressure (psi : Unit → Real)
    (theta : Real) : Real :=
  Real.log (Real.exp (theta * psi ()))

theorem paper_xi_time_part9xc_serrin_geometry_all_cumulants_vanish (psi : Unit → Real) :
    ∀ theta : Real,
      xi_time_part9xc_serrin_geometry_all_cumulants_vanish_pressure psi theta = theta * psi () := by
  intro theta
  rw [xi_time_part9xc_serrin_geometry_all_cumulants_vanish_pressure, Real.log_exp]

end Omega.Zeta
