import Omega.Zeta.XiTerminalZmS3EndoscopicPrymA2Coxeter

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-prym-polarization-a2-rigidity`.  This is the paper-facing
wrapper for the existing `S₃` endoscopic Prym `A₂` polarization and Coxeter action package. -/
theorem paper_xi_terminal_zm_prym_polarization_a2_rigidity :
    xiTerminalZmS3EndoscopicPrymPolarizationIsA2 ∧
      xiTerminalZmS3EndoscopicPrymPolarizationType = (1, 3) ∧
      xiTerminalZmS3EndoscopicDeckActsByA2Coxeter := by
  exact paper_xi_terminal_zm_s3_endoscopic_prym_a2_coxeter

end Omega.Zeta
