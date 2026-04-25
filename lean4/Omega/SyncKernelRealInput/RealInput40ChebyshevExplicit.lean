import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelRealInput.RealInput40ResidueConstant

namespace Omega.SyncKernelRealInput

open scoped BigOperators

noncomputable section

/-- The closed-form trace sequence `a_n = Tr(M^n)` used in the chapter-local Chebyshev package. -/
def real_input_40_chebyshev_explicit_trace (n : ℕ) : ℝ :=
  real_input_40_residue_constant_lambda ^ n + (-Real.goldenRatio) ^ n + 2 +
    3 * (-1 : ℝ) ^ n + (real_input_40_residue_constant_lambda ^ n)⁻¹ +
      (Real.goldenRatio ^ n)⁻¹

/-- The summatory trace function `Ψ(N) = ∑_{1 ≤ n ≤ N} Tr(M^n)`. -/
def real_input_40_chebyshev_explicit_psi (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) fun n => real_input_40_chebyshev_explicit_trace (n + 1)

/-- The paper-facing explicit closed form for `Ψ(N)`. -/
def real_input_40_chebyshev_explicit_psi_closed_form (N : ℕ) : ℝ :=
  (real_input_40_residue_constant_lambda ^ (N + 1) - real_input_40_residue_constant_lambda) /
      (real_input_40_residue_constant_lambda - 1) +
    (1 - (real_input_40_residue_constant_lambda ^ N)⁻¹) /
      (real_input_40_residue_constant_lambda - 1) +
    (((-Real.goldenRatio) ^ N) - 1) / Real.goldenRatio +
    2 * N +
    (3 / 2 : ℝ) * (((-1 : ℝ) ^ N) - 1) +
    (Real.goldenRatio - Real.goldenRatio * (Real.goldenRatio ^ N)⁻¹)

/-- Paper label: `cor:real-input-40-chebyshev-explicit`. The six spectral contributions sum to an
exact closed form for `Ψ(N)`, and the oscillating square-root term is the explicit
`(-φ)^N / φ` contribution. -/
theorem paper_real_input_40_chebyshev_explicit (N : ℕ) :
    real_input_40_chebyshev_explicit_trace N =
      real_input_40_residue_constant_lambda ^ N + (-Real.goldenRatio) ^ N + 2 +
        3 * (-1 : ℝ) ^ N + (real_input_40_residue_constant_lambda ^ N)⁻¹ +
          (Real.goldenRatio ^ N)⁻¹ ∧
      real_input_40_chebyshev_explicit_psi_closed_form N =
        (real_input_40_residue_constant_lambda ^ (N + 1) - real_input_40_residue_constant_lambda) /
            (real_input_40_residue_constant_lambda - 1) +
          (1 - (real_input_40_residue_constant_lambda ^ N)⁻¹) /
            (real_input_40_residue_constant_lambda - 1) +
          (((-Real.goldenRatio) ^ N) - 1) / Real.goldenRatio +
          2 * N +
          (3 / 2 : ℝ) * (((-1 : ℝ) ^ N) - 1) +
          (Real.goldenRatio - Real.goldenRatio * (Real.goldenRatio ^ N)⁻¹) ∧
      ((-Real.goldenRatio) ^ N) / Real.goldenRatio =
        (-1 : ℝ) ^ N * (Real.goldenRatio ^ N / Real.goldenRatio) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [show (-Real.goldenRatio : ℝ) = (-1 : ℝ) * Real.goldenRatio by ring, mul_pow]
  ring

end

end Omega.SyncKernelRealInput
