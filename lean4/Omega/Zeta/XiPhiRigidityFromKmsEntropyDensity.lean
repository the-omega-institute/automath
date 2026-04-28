import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-phi-rigidity-from-kms-entropy-density`. -/
theorem paper_xi_phi_rigidity_from_kms_entropy_density
    (lambda beta entropyDensity : ℝ)
    (hlambda : lambda = Real.exp (-beta))
    (hbeta : Real.exp beta = Real.goldenRatio)
    (hentropy : entropyDensity = Real.log 2 - beta) :
    lambda = Real.goldenRatio⁻¹ ∧ beta = Real.log Real.goldenRatio ∧
      entropyDensity = Real.log (2 / Real.goldenRatio) := by
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hbeta_log : beta = Real.log Real.goldenRatio := by
    calc
      beta = Real.log (Real.exp beta) := (Real.log_exp beta).symm
      _ = Real.log Real.goldenRatio := by rw [hbeta]
  refine ⟨?_, ?_, ?_⟩
  · rw [hlambda, hbeta_log, Real.exp_neg, Real.exp_log hphi_pos]
  · exact hbeta_log
  · rw [hentropy, hbeta_log]
    exact (Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hphi_pos.ne').symm

end Omega.Zeta
