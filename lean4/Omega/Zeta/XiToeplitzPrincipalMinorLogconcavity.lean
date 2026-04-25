import Mathlib.Tactic
import Omega.Zeta.XiToeplitzPrincipalMinorDiscreteCurvatureRecovery

namespace Omega.Zeta

open XiToeplitzDetVerblunskyData

open scoped BigOperators

noncomputable section

/-- Paper label: `cor:xi-toeplitz-principal-minor-logconcavity`. In the cumulative
principal-minor model from the Toeplitz determinant recursion, the discrete-curvature ratio is
exactly `1 - |α_N|²`; since this quantity is at most `1`, the cumulative principal minors are
log-concave at every good index. -/
theorem paper_xi_toeplitz_principal_minor_logconcavity
    (steps N : ℕ) (delta0 : ℝ) (hdelta0 : 0 < delta0) (alpha : Fin steps → ℝ)
    (hgood : ∀ j : Fin steps, |alpha j| < 1) (hN : N < steps) :
    let D : XiToeplitzDetVerblunskyData :=
      { steps := steps, delta0 := delta0, hdelta0 := hdelta0, alpha := alpha }
    D.discreteCurvature N = 1 - |D.alphaAt N| ^ 2 ∧
      D.cumulativePrincipalMinor (N + 2) * D.cumulativePrincipalMinor N ≤
        D.cumulativePrincipalMinor (N + 1) ^ 2 := by
  let D : XiToeplitzDetVerblunskyData :=
    { steps := steps, delta0 := delta0, hdelta0 := hdelta0, alpha := alpha }
  have hgoodD : ∀ j < D.steps, |D.alphaAt j| < 1 := by
    intro j hj
    simp [D, XiToeplitzDetVerblunskyData.alphaAt, hj, hgood ⟨j, hj⟩]
  have hcurv : D.discreteCurvature N = 1 - |D.alphaAt N| ^ 2 :=
    D.discreteCurvature_eq_one_sub_abs_sq hgoodD hN
  have hcurv_le_one : D.discreteCurvature N ≤ 1 := by
    rw [hcurv]
    nlinarith [sq_nonneg (|D.alphaAt N|)]
  have hcum_pos : 0 < D.cumulativePrincipalMinor (N + 1) := by
    have hNp1 : N + 1 ≤ D.steps + 1 := by
      simpa [D] using Nat.succ_le_succ (Nat.le_of_lt hN)
    exact D.cumulativePrincipalMinor_pos hgoodD hNp1
  have hsq_pos : 0 < D.cumulativePrincipalMinor (N + 1) ^ 2 := sq_pos_of_pos hcum_pos
  have hlogconc :
      D.cumulativePrincipalMinor (N + 2) * D.cumulativePrincipalMinor N ≤
        D.cumulativePrincipalMinor (N + 1) ^ 2 := by
    have := (div_le_iff₀ hsq_pos).mp hcurv_le_one
    simpa [XiToeplitzDetVerblunskyData.discreteCurvature] using this
  simpa [D] using And.intro hcurv hlogconc

end

end Omega.Zeta
