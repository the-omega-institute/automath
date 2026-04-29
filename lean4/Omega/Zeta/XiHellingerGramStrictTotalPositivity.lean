import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic
import Omega.Zeta.XiHellingerKernelFourierSech2

namespace Omega.Zeta

/-- The explicit `2 × 2` Hellinger Gram witness at gaps `0` and `1`: positivity of the entries,
strict positivity of the `2 × 2` determinant, and the resulting strict separation of the two
eigenvalue surrogates `k0 ± k1`. This is the concrete finite witness used here for the strict
total-positivity package.
    thm:xi-hellinger-gram-strict-total-positivity -/
theorem paper_xi_hellinger_gram_strict_total_positivity :
    let k0 := xiHellingerKernelFourierDensity 0
    let k1 := xiHellingerKernelFourierDensity 1
    0 < k1 ∧
      k1 < k0 ∧
      0 < k0 ^ 2 - k1 ^ 2 ∧
      0 < k0 - k1 ∧
      k0 - k1 < k0 + k1 := by
  dsimp
  rcases paper_xi_hellinger_kernel_fourier_sech2 with ⟨hfourier, hmass⟩
  have hk0 : xiHellingerKernelFourierDensity 0 = Real.pi ^ 2 := by
    simpa [xiHellingerKernelMass] using hmass
  have hk1 : xiHellingerKernelFourierDensity 1 = Real.pi ^ 2 / (Real.cosh Real.pi) ^ 2 := by
    simpa using hfourier 1
  have hcosh_gt : 1 < Real.cosh Real.pi := by
    exact (Real.one_lt_cosh).2 Real.pi_pos.ne'
  have hden_pos : 0 < (Real.cosh Real.pi) ^ 2 := by
    positivity
  have hden_gt : 1 < (Real.cosh Real.pi) ^ 2 := by
    nlinarith [hcosh_gt, Real.cosh_pos Real.pi]
  have hpi_sq_pos : 0 < Real.pi ^ 2 := by
    positivity
  have hk1_pos : 0 < xiHellingerKernelFourierDensity 1 := by
    rw [hk1]
    positivity
  have hk1_lt : xiHellingerKernelFourierDensity 1 < xiHellingerKernelFourierDensity 0 := by
    rw [hk1, hk0]
    field_simp [hden_pos.ne']
    nlinarith [hpi_sq_pos, hden_gt]
  refine ⟨hk1_pos, hk1_lt, ?_, ?_, ?_⟩
  · nlinarith [hk1_pos, hk1_lt]
  · nlinarith [hk1_lt]
  · nlinarith [hk1_pos]

end Omega.Zeta
