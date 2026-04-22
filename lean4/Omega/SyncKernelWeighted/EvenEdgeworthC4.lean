import Mathlib.Tactic
import Omega.SyncKernelWeighted.EdgeworthSixEight
import Omega.SyncKernelWeighted.PrimitiveFiniteSym

namespace Omega.SyncKernelWeighted

/-- Paper label: `thm:sync-kernel-even-edgeworth-c4`.
Palindromic primitive profiles have symmetry center `n / 2`, all odd centered moments vanish, and
the audited first even Edgeworth coefficient is the recorded rational constant. -/
theorem paper_sync_kernel_even_edgeworth_c4 (n m : ℕ) (a : ℕ → ℚ)
    (hpal : ∀ k, k ≤ n → a k = a (n - k)) (hmass : primitiveFiniteMass n a ≠ 0) :
    primitiveFiniteMean n a = (n : ℚ) / 2 ∧
      primitiveFiniteOddCenteredMoment n m a = 0 ∧
      edgeworthKappa4 / (24 * edgeworthSigmaSq ^ 2) = 1559 / 16456 := by
  rcases paper_primitive_finite_sym n m a hpal hmass with ⟨hMean, hOdd⟩
  refine ⟨hMean, hOdd, ?_⟩
  norm_num [edgeworthKappa4, edgeworthSigmaSq]

end Omega.SyncKernelWeighted
