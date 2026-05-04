import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-pick-poisson-condition-number-certificate`. -/
theorem paper_xi_pick_poisson_condition_number_certificate {k : ℕ}
    {lambdaMax lambdaMin pSigma det prodp prodrho : ℝ} (hk : 1 ≤ k)
    (hlmin : 0 < lambdaMin) (hps : 0 < pSigma) (hdet : 0 < det)
    (hmax : lambdaMax ≤ pSigma) (hgap : det / pSigma ^ (k - 1) ≤ lambdaMin)
    (hfactor : det = prodp * prodrho) :
    lambdaMax / lambdaMin ≤ pSigma ^ k / (prodp * prodrho) := by
  have hpow_pos : 0 < pSigma ^ (k - 1) := pow_pos hps _
  have hgap_pos : 0 < det / pSigma ^ (k - 1) := div_pos hdet hpow_pos
  have hbound :
      lambdaMax / lambdaMin ≤ pSigma / (det / pSigma ^ (k - 1)) := by
    calc
      lambdaMax / lambdaMin ≤ pSigma / lambdaMin := by
        exact div_le_div_of_nonneg_right hmax hlmin.le
      _ ≤ pSigma / (det / pSigma ^ (k - 1)) := by
        exact div_le_div_of_nonneg_left hps.le hgap_pos hgap
  have halg :
      pSigma / (det / pSigma ^ (k - 1)) = pSigma ^ k / det := by
    have hpow_ne : pSigma ^ (k - 1) ≠ 0 := hpow_pos.ne'
    have hdet_ne : det ≠ 0 := hdet.ne'
    rw [show pSigma ^ k = pSigma ^ (k - 1) * pSigma by
      rw [← pow_succ, Nat.sub_add_cancel hk]]
    field_simp [hpow_ne, hdet_ne]
  have htarget : lambdaMax / lambdaMin ≤ pSigma ^ k / det := by
    simpa [halg] using hbound
  simpa [hfactor] using htarget

end Omega.Zeta
