import Mathlib

open scoped Matrix

namespace Omega.Zeta

noncomputable section

/-- Vandermonde-diagonal main term for the finite recovery window. -/
def xi_logcm_finite_window_bernoulli_recovery_main {κ : ℕ}
    (V : Matrix (Fin κ) (Fin κ) ℝ) (diag coeff : Fin κ → ℝ) : Fin κ → ℝ :=
  V.mulVec fun r => diag r * coeff r

/-- Window observations are the Vandermonde-diagonal main term plus an error vector. -/
def xi_logcm_finite_window_bernoulli_recovery_observation {κ : ℕ}
    (V : Matrix (Fin κ) (Fin κ) ℝ) (diag coeff error : Fin κ → ℝ) : Fin κ → ℝ :=
  xi_logcm_finite_window_bernoulli_recovery_main V diag coeff + error

/-- Componentwise recovery after multiplying by the inverse Vandermonde matrix. -/
def xi_logcm_finite_window_bernoulli_recovery_recovered {κ : ℕ}
    (Vinv : Matrix (Fin κ) (Fin κ) ℝ) (diag observation : Fin κ → ℝ) : Fin κ → ℝ :=
  fun r => (diag r)⁻¹ * (Vinv.mulVec observation) r

lemma xi_logcm_finite_window_bernoulli_recovery_recovered_sub {κ : ℕ}
    (V Vinv : Matrix (Fin κ) (Fin κ) ℝ) (diag coeff error : Fin κ → ℝ)
    (hleft : Vinv * V = 1) (hdiag : ∀ r, diag r ≠ 0) (r : Fin κ) :
    xi_logcm_finite_window_bernoulli_recovery_recovered Vinv diag
        (xi_logcm_finite_window_bernoulli_recovery_observation V diag coeff error) r -
      coeff r =
        (diag r)⁻¹ * (Vinv.mulVec error) r := by
  have hmul :
      Vinv.mulVec (V.mulVec fun s => diag s * coeff s) = fun s => diag s * coeff s := by
    rw [Matrix.mulVec_mulVec, hleft]
    ext s
    simp
  unfold xi_logcm_finite_window_bernoulli_recovery_recovered
    xi_logcm_finite_window_bernoulli_recovery_observation
    xi_logcm_finite_window_bernoulli_recovery_main
  rw [Matrix.mulVec_add, hmul]
  simp only [Pi.add_apply]
  field_simp [hdiag r]
  ring

/-- Paper label: `cor:xi-logcm-finite-window-bernoulli-recovery`.

Multiplying the finite window equation by the inverse Vandermonde matrix recovers each Bernoulli
coefficient up to the inverse-transformed error, hence any exponential bound for that transformed
error gives the same componentwise exponential recovery estimate. -/
theorem paper_xi_logcm_finite_window_bernoulli_recovery {κ : ℕ}
    (V Vinv : Matrix (Fin κ) (Fin κ) ℝ) (diag coeff error : Fin κ → ℝ) (C η : ℝ) (N : ℕ)
    (hleft : Vinv * V = 1) (hdiag : ∀ r, diag r ≠ 0)
    (herror :
      ∀ r,
        |(diag r)⁻¹ * (Vinv.mulVec error) r| ≤ C * Real.exp (-η * (N : ℝ))) :
    ∀ r,
      |xi_logcm_finite_window_bernoulli_recovery_recovered Vinv diag
            (xi_logcm_finite_window_bernoulli_recovery_observation V diag coeff error) r -
          coeff r| ≤
        C * Real.exp (-η * (N : ℝ)) := by
  intro r
  rw [xi_logcm_finite_window_bernoulli_recovery_recovered_sub V Vinv diag coeff error hleft
    hdiag r]
  exact herror r

end

end Omega.Zeta
