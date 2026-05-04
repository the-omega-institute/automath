import Mathlib.Tactic
import Omega.Zeta.XiKernelDirichletZetaFiniteEulerCorrection
import Omega.Zeta.XiKernelLossDivisibilityValuationRationalEuler

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-kernel-dirichlet-euler-rational-smith-completeness`.
The local Smith-prefix kernel package supplies the stabilized prime-power tail, the finite Euler
correction, and the second-difference recovery of Smith exponent multiplicities. -/
theorem paper_xi_kernel_dirichlet_euler_rational_smith_completeness :
    XiKernelLossDivisibilityValuationRationalEulerLaw ∧
      xi_kernel_dirichlet_zeta_finite_euler_correction_statement ∧
      (∀ {m : ℕ} (e : Fin m → ℕ) (k : ℕ),
        smithPrefixTop e ≤ k → smithPrefixValue e k = ∑ i, e i) ∧
      (∀ {m : ℕ} (e : Fin m → ℕ) (ℓ : ℕ),
        smithPrefixMultiplicity e ℓ =
          smithPrefixDelta e ℓ - smithPrefixDelta e (ℓ + 1)) := by
  refine ⟨paper_xi_kernel_loss_divisibility_valuation_rational_euler, ?_, ?_, ?_⟩
  · exact paper_xi_kernel_dirichlet_zeta_finite_euler_correction
  · intro m e k hk
    exact smithPrefixValue_eq_total_of_le_top e k hk
  · intro m e ℓ
    exact smithPrefixMultiplicity_eq_delta_sub_delta e ℓ

end Omega.Zeta
