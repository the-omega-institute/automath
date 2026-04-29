import Mathlib.Tactic

namespace Omega

/-- Paper label: `cor:pom-centralizer-fpdim-golden`. -/
theorem paper_pom_centralizer_fpdim_golden (fpdim_tau rho_M phi : Real)
    (hfp : fpdim_tau = rho_M) (hrho : rho_M = phi) : fpdim_tau = phi := by
  exact hfp.trans hrho

end Omega
