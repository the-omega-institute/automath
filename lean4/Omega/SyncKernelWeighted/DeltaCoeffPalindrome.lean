import Omega.SyncKernelWeighted.TracePalindrome

namespace Omega.SyncKernelWeighted

/-- Paper label: `cor:delta-coeff-palindrome`. The completed trace-palindrome identity already
provides the coefficientwise inversion law for the concrete family `(u + 1)^j`. -/
theorem paper_delta_coeff_palindrome : ∀ j : Fin 11, ∀ u : ℚ, u ≠ 0 →
    (u + 1) ^ j.1 = u ^ j.1 * (u⁻¹ + 1) ^ j.1 := by
  intro j u hu
  simpa [tracePalindromeFamily] using tracePalindromeFamily_inversion j.1 hu

end Omega.SyncKernelWeighted
