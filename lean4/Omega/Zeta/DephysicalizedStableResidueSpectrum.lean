import Mathlib.Data.ZMod.Basic
import Omega.SyncKernelWeighted.WittThetaStableResidue

namespace Omega.Zeta

/-- Paper label: `thm:dephys-stable-residue-spectrum`. The existing stable-residue theorem
supplies stage-independence; package the common value as an existential invariant. -/
theorem paper_dephys_stable_residue_spectrum (p r : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r)
    (A : ℕ → ℤ) (hscale : Omega.SyncKernelWeighted.wittThetaDerivativeScaling p r A) :
    ∃ alpha : ZMod p,
      ∀ k, 1 ≤ k →
        Omega.SyncKernelWeighted.witt_theta_stable_residue_normalized p A k = alpha := by
  refine ⟨Omega.SyncKernelWeighted.witt_theta_stable_residue_normalized p A 1, ?_⟩
  exact Omega.SyncKernelWeighted.paper_witt_theta_stable_residue p r hp hr A hscale

end Omega.Zeta
