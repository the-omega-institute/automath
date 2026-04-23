import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmS3EndoscopicHomologyA2Identification
import Omega.Zeta.XiTerminalZmS3RootRecoveryCoordinateAutomorphisms

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-s3-closure-jacobian-splitting`.
The indexed root-recovery theorem supplies the `S₃` action on the ordered resolvent roots; the
endoscopic `A₂` package identifies the standard two-dimensional block; and the Jacobian splitting
package records one base genus-`2` factor together with two copies of the elliptic resolvent
factor. -/
theorem paper_xi_terminal_zm_s3_closure_jacobian_splitting
    {y z1 z2 z3 w dRdz : ℚ} (hdRdz : dRdz ≠ 0)
    (hsum : z2 + z3 = -((1 + 2 * y) + z1))
    (hdiff : z2 - z3 = w / dRdz) :
    z2 = -((1 + 2 * y) + z1) / 2 + w / (2 * dRdz) ∧
      z3 = -((1 + 2 * y) + z1) / 2 - w / (2 * dRdz) ∧
      xiTerminalZmS3SigmaPermutesRoots z1 z2 z3 ∧
      xiTerminalZmS3IotaSwapsConjugates z1 z2 z3 ∧
      xiTerminalZmS3GeneratesS3 ∧
      xiTerminalZmS3EndoscopicPrymPolarizationIsA2 ∧
      xiTerminalZmS3EndoscopicPrymPolarizationType = (1, 3) ∧
      xiTerminalZmS3JacobianSplitting := by
  have hRoot :
      z2 = -((1 + 2 * y) + z1) / 2 + w / (2 * dRdz) ∧
        z3 = -((1 + 2 * y) + z1) / 2 - w / (2 * dRdz) ∧
        xiTerminalZmS3SigmaPermutesRoots z1 z2 z3 ∧
        xiTerminalZmS3IotaSwapsConjugates z1 z2 z3 ∧
        xiTerminalZmS3GeneratesS3 :=
    paper_xi_terminal_zm_s3_root_recovery_coordinate_automorphisms_indexed hdRdz hsum hdiff
  have hPrym := paper_xi_terminal_zm_s3_endoscopic_prym_a2_coxeter
  have hSplit := paper_xi_terminal_zm_s3_endoscopic_homology_a2_identification
  exact ⟨hRoot.1, hRoot.2.1, hRoot.2.2.1, hRoot.2.2.2.1, hRoot.2.2.2.2,
    hPrym.1, hPrym.2.1, hSplit.2.2⟩

end Omega.Zeta
