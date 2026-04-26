import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `thm:gm-add-mult-energy-complementarity`. The conditional tensor-transducer
gap immediately subtracts the positive interior margin from the combined logarithmic energy. -/
theorem paper_gm_add_mult_energy_complementarity (alpha beta_add beta_mul kappa : ℝ)
    (halpha : 1 < alpha) (hbeta_add : 0 < beta_add) (hbeta_mul : 0 < beta_mul)
    (hkappa : 0 < kappa)
    (hTensorGap : Real.log beta_add + Real.log beta_mul + kappa ≤ 6 * Real.log alpha) :
    Real.log beta_add + Real.log beta_mul ≤ 6 * Real.log alpha - kappa := by
  have _halpha := halpha
  have _hbeta_add := hbeta_add
  have _hbeta_mul := hbeta_mul
  have _hkappa := hkappa
  linarith

end Omega.SyncKernelRealInput
