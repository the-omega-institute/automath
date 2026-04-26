import Omega.SyncKernelWeighted.AbelMertensConstantUniversal
import Omega.SyncKernelWeighted.MuPochhammerDecomposition

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete synchronized-kernel package for the paper's finite-part `μ`-Pochhammer closed form:
the finite spectral decomposition is the exact Möbius/Pochhammer expansion, and the Abel
finite-part constant is the certified closed-form branch extracted from the same package. -/
def finite_part_mu_pochhammer_spectral_closed_form_statement : Prop :=
  (∀ (spectrum : Finset ℂ) (mult : ℂ → ℕ) (mobius : ℕ → ℂ) (z : ℂ) (N : ℕ),
    mu_pochhammer_decomposition_mobius_log spectrum mult mobius z N =
      -(Finset.sum spectrum fun eig =>
        (mult eig : ℂ) * mu_pochhammer_decomposition_pochhammer_log eig mobius z N)) ∧
    (∀ D : SyncKernelAbelMertensAnalyticFamilyData, paper_abel_mertens_constant_universal D)

/-- Paper label: `thm:finite-part-mu-pochhammer-spectral-closed-form`. -/
theorem paper_finite_part_mu_pochhammer_spectral_closed_form :
    finite_part_mu_pochhammer_spectral_closed_form_statement := by
  refine ⟨?_, ?_⟩
  · intro spectrum mult mobius z N
    exact paper_mu_pochhammer_decomposition spectrum mult mobius z N
  · intro D
    exact abel_mertens_constant_universal_certified D

end

end Omega.SyncKernelWeighted
