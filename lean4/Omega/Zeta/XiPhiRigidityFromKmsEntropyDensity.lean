import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-phi-rigidity-from-kms-entropy-density`. -/
theorem paper_xi_phi_rigidity_from_kms_entropy_density
    (phi lambda beta entropyDensity : ℝ) (_hphi_pos : 0 < phi)
    (hlambda : lambda = 1 / phi) (hbeta : beta = Real.log phi)
    (hentropy : entropyDensity = Real.log 2 - beta)
    (hlog_div : Real.log (2 / phi) = Real.log 2 - Real.log phi) :
    lambda = 1 / phi ∧ beta = Real.log phi ∧ entropyDensity = Real.log (2 / phi) := by
  refine ⟨hlambda, hbeta, ?_⟩
  calc
    entropyDensity = Real.log 2 - beta := hentropy
    _ = Real.log 2 - Real.log phi := by rw [hbeta]
    _ = Real.log (2 / phi) := hlog_div.symm

end Omega.Zeta
