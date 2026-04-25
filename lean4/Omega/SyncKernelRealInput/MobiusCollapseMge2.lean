import Omega.SyncKernelRealInput.MobiusCollapseMge2Ab

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Paper label: `lem:mobius-collapse-mge2`. The two `m ≥ 2` branch identities are the first two
components of the existing coefficient-parametrized Möbius-collapse package. -/
theorem paper_mobius_collapse_mge2 (z : ℂ) (hz : ‖z‖ < 1) :
    mobius_collapse_mge2_ab_one_minus z = -z - Complex.log (1 - z) ∧
      mobius_collapse_mge2_ab_one_plus z = z - z ^ (2 : ℕ) - Complex.log (1 + z) := by
  rcases paper_mobius_collapse_mge2_ab 0 0 z hz with ⟨hminus, hplus, _⟩
  exact ⟨hminus, hplus⟩

end

end Omega.SyncKernelRealInput
