import Mathlib.Algebra.Polynomial.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelRealInput.RealInput40SpectrumDecomp
import Omega.SyncKernelWeighted.RealInput40Essential20
import Omega.SyncKernelWeighted.RealInput40EssentialReduction
import Omega.SyncKernelWeighted.RealInput40NilpotentIndex

namespace Omega.Conclusion

open Omega.SyncKernelWeighted
open Omega.SyncKernelRealInput

open scoped goldenRatio

noncomputable section

/-- Paper-facing package for
`thm:conclusion-realinput40-legality-memory-spectral-aphasia`. The concrete legality audit is the
unique `20`-state essential core inside the `40`-state model; the transient shell contributes
only the stripped zero spectrum, while the nonzero spectrum is the explicit Fibonacci/sign/trivial
list already audited in the real-input chapter. -/
def conclusion_realinput40_legality_memory_spectral_aphasia_statement : Prop :=
  realInput40Vertices.card = 40 ∧
    realInput40EssentialCore.card = 20 ∧
    realInput40TransientShell.card = 20 ∧
    (∀ i ∈ realInput40EssentialCore, ∀ j ∈ realInput40EssentialCore, realInput40CoreReachable i j) ∧
    (∀ D : RealInput40EssentialReductionData, RealInput40EssentialReduction D) ∧
    real_input_40_nilpotent_index_essential_kernel_dim 3 = 11 ∧
    real_input_40_nilpotent_index_full_kernel_dim 5 = 31 ∧
    (∀ k : ℕ, 5 ≤ k → real_input_40_nilpotent_index_full_kernel_dim k = 31) ∧
    real_input_40_spectrum_decomp_nonzeroSpectrum =
      [Real.goldenRatio ^ (2 : ℕ), 1, 1, (Real.goldenRatio ^ (2 : ℕ))⁻¹,
        -Real.goldenRatio, -(Real.goldenRatio⁻¹), 1, 1, -1] ∧
    triv_factor_primitive_polynomial_ptriv = -Polynomial.X + Polynomial.C 3 * Polynomial.X ^ 2

/-- Paper label: `thm:conclusion-realinput40-legality-memory-spectral-aphasia`. -/
theorem paper_conclusion_realinput40_legality_memory_spectral_aphasia :
    conclusion_realinput40_legality_memory_spectral_aphasia_statement := by
  rcases paper_real_input_40_essential_20 with
    ⟨hVertices, _, _, _, _, hCore, hTransient, hReach, _, _, _⟩
  rcases paper_real_input_40_nilpotent_index with
    ⟨_, _, hEss3, _, _, _, _, _, hFull5, hStable⟩
  rcases paper_real_input_40_spectrum_decomp with
    ⟨_, hTrivial, _, _, _, hSpectrum⟩
  refine ⟨hVertices, hCore, hTransient, hReach, ?_, hEss3, hFull5, hStable, hSpectrum, hTrivial⟩
  intro D
  exact paper_real_input_40_essential_reduction D

end

end Omega.Conclusion
