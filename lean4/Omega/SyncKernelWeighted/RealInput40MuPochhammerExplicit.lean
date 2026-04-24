import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelRealInput
import Omega.SyncKernelWeighted.FinitePartMuPochhammerSpectralClosedForm
import Omega.SyncKernelWeighted.MuPochhammerPhi1ExpMinusZ
import Omega.SyncKernelWeighted.RealInput40Essential20

namespace Omega.SyncKernelWeighted

open Polynomial

noncomputable section

/-- Paper label: `cor:real-input-40-mu-pochhammer-explicit`. The audited `40`-state package
combines the `20`-state essential-core decomposition, the explicit nonzero-spectrum list, the
generic finite `μ`-Pochhammer factorization, and the collapsed trivial-factor polynomial
`-z + 3 z²`. -/
theorem paper_real_input_40_mu_pochhammer_explicit :
    realInput40Vertices.card = 40 ∧
      realInput40EssentialCore.card = 20 ∧
      Omega.SyncKernelRealInput.real_input_40_spectrum_decomp_nonzeroSpectrum =
        [Real.goldenRatio ^ (2 : ℕ), 1, 1, (Real.goldenRatio ^ (2 : ℕ))⁻¹,
          -Real.goldenRatio, -(Real.goldenRatio⁻¹), 1, 1, -1] ∧
      (Omega.SyncKernelRealInput.triv_factor_primitive_polynomial_ptriv =
        (-Polynomial.X + Polynomial.C 3 * Polynomial.X ^ 2)) ∧
      (∀ (spectrum : Finset ℂ) (mult : ℂ → ℕ) (mobius : ℕ → ℂ) (z : ℂ) (N : ℕ),
        mu_pochhammer_decomposition_mobius_log spectrum mult mobius z N =
          -(Finset.sum spectrum fun eig =>
            (mult eig : ℂ) * mu_pochhammer_decomposition_pochhammer_log eig mobius z N)) ∧
      (∀ z : ℂ,
        mu_pochhammer_phi1_exp_minus_z_log z = -z ∧
          ((-2 : ℂ) * mu_pochhammer_phi1_exp_minus_z_log z +
              (-3 : ℂ) * (z - z ^ 2) =
            -z + 3 * z ^ 2)) := by
  rcases paper_real_input_40_essential_20 with
    ⟨hVertices, _, _, _, _, hEssential, _, _, _, _, _⟩
  rcases Omega.SyncKernelRealInput.paper_real_input_40_spectrum_decomp with
    ⟨_, hTrivial, _, _, _, hSpectrum⟩
  rcases paper_finite_part_mu_pochhammer_spectral_closed_form with ⟨hDecomp, _⟩
  rcases paper_mu_pochhammer_phi1_exp_minus_z with ⟨_, hPhi1⟩
  refine ⟨hVertices, hEssential, hSpectrum, hTrivial, hDecomp, ?_⟩
  intro z
  rcases hPhi1 z with ⟨hz, _⟩
  refine ⟨hz, ?_⟩
  simp [hz]
  ring

end

end Omega.SyncKernelWeighted
