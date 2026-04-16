import Omega.TypedAddressBiaxialCompletion.ComovingDefectBound

namespace Omega.TypedAddressBiaxialCompletion

/-- The paper's uniform minimization threshold
    `Δₙ = (1 - ρₙ e^{-εₙ}) / (1 + ρₙ e^{-εₙ})`. -/
noncomputable def comovingUniformThreshold (rho eps : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 - rho n * Real.exp (-eps n)) / (1 + rho n * Real.exp (-eps n))

/-- Paper-facing uniform minimization wrapper:
    specialize the comoving defect bound at the aligned chart `x₀ = γ`, use the uniform chart
    bound to replace `D n γ` by `εₙ`, and rewrite `δ = 1/2 - β`.
    thm:typed-address-biaxial-completion-comoving-uniform-minimization -/
theorem paper_typed_address_biaxial_completion_comoving_uniform_minimization
    (rho eps : ℕ → ℝ) (D : ℕ → ℝ → ℝ) (beta gamma : ℝ)
    (hrho : ∀ n, 0 < rho n) (hrho_lt : ∀ n, rho n < 1) (heps : ∀ n, 0 ≤ eps n)
    (hbeta : beta ≤ 1 / 2)
    (huniform : ∀ n x0, D n x0 ≤ eps n)
    (hdefect :
      ∀ n, rho n * Real.exp (-(D n gamma)) ≤ (1 - (1 / 2 - beta)) / (1 + (1 / 2 - beta))) :
    ∀ n, 1 / 2 - comovingUniformThreshold rho eps n ≤ beta := by
  intro n
  have hrho_nonneg : 0 ≤ rho n := le_of_lt (hrho n)
  have hdelta : 0 ≤ 1 / 2 - beta := by linarith
  have hexp :
      Real.exp (-eps n) ≤ Real.exp (-(D n gamma)) := by
    apply Real.exp_le_exp.mpr
    linarith [huniform n gamma]
  have hbound_eps :
      rho n * Real.exp (-eps n) ≤ (1 - (1 / 2 - beta)) / (1 + (1 / 2 - beta)) := by
    have hmul := mul_le_mul_of_nonneg_left hexp hrho_nonneg
    exact le_trans hmul (hdefect n)
  have hdelta_bound :
      1 / 2 - beta ≤ comovingUniformThreshold rho eps n := by
    simpa [comovingUniformThreshold] using
      paper_typed_address_biaxial_completion_comoving_defect_bound
        (hrho n) (hrho_lt n) (heps n) hdelta hbound_eps
  linarith

end Omega.TypedAddressBiaxialCompletion
