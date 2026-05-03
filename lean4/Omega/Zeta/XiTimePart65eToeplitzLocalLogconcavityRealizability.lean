import Omega.Zeta.XiToeplitzPrincipalMinorDiscreteCurvatureRecovery

namespace Omega.Zeta

open XiToeplitzDetVerblunskyData

open scoped BigOperators

noncomputable section

/-- Paper label: `thm:xi-time-part65e-toeplitz-local-logconcavity-realizability`. -/
theorem paper_xi_time_part65e_toeplitz_local_logconcavity_realizability
    (steps : ℕ) (delta0 : ℝ) (hdelta0 : 0 < delta0) (alpha : Fin steps → ℝ)
    (hgood : ∀ j : Fin steps, |alpha j| < 1) :
    let D : XiToeplitzDetVerblunskyData :=
      { steps := steps, delta0 := delta0, hdelta0 := hdelta0, alpha := alpha }
    (∀ k < steps,
      D.cumulativePrincipalMinor (k + 2) * D.cumulativePrincipalMinor k ≤
        D.cumulativePrincipalMinor (k + 1) ^ 2) ∧
      (∀ k < steps, D.discreteCurvature k = 1 - |D.alphaAt k| ^ 2) := by
  let D : XiToeplitzDetVerblunskyData :=
    { steps := steps, delta0 := delta0, hdelta0 := hdelta0, alpha := alpha }
  have hgoodD : ∀ j < D.steps, |D.alphaAt j| < 1 := by
    intro j hj
    simpa [D, XiToeplitzDetVerblunskyData.alphaAt, hj] using hgood ⟨j, hj⟩
  have hcurv_all : ∀ k < D.steps, D.discreteCurvature k = 1 - |D.alphaAt k| ^ 2 :=
    (paper_xi_toeplitz_principal_minor_discrete_curvature_recovery D hgoodD).1
  have hlogconc :
      ∀ k < D.steps,
        D.cumulativePrincipalMinor (k + 2) * D.cumulativePrincipalMinor k ≤
          D.cumulativePrincipalMinor (k + 1) ^ 2 := by
    intro k hk
    have hcurv : D.discreteCurvature k = 1 - |D.alphaAt k| ^ 2 := hcurv_all k hk
    have hcurv_le_one : D.discreteCurvature k ≤ 1 := by
      rw [hcurv]
      nlinarith [sq_nonneg (|D.alphaAt k|)]
    have hcum_pos : 0 < D.cumulativePrincipalMinor (k + 1) := by
      exact D.cumulativePrincipalMinor_pos hgoodD (by omega)
    have hsq_pos : 0 < D.cumulativePrincipalMinor (k + 1) ^ 2 := sq_pos_of_pos hcum_pos
    have := (div_le_iff₀ hsq_pos).mp hcurv_le_one
    simpa [XiToeplitzDetVerblunskyData.discreteCurvature] using this
  simpa [D] using And.intro hlogconc hcurv_all

end

end Omega.Zeta
