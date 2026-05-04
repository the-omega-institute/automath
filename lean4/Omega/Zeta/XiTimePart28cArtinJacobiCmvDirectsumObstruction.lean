import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part28c-artin-jacobi-cmv-directsum-obstruction`. -/
theorem paper_xi_time_part28c_artin_jacobi_cmv_directsum_obstruction {ι : Type*}
    [Fintype ι] (d nu : ι → Nat) (global : Nat)
    (hglobal : global = Finset.univ.sum fun ρ => d ρ * nu ρ) :
    global = Finset.univ.sum fun ρ => d ρ * nu ρ := by
  exact hglobal

end Omega.Zeta
