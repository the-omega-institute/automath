import Omega.Zeta.SyncKernelPalindrome

namespace Omega.Zeta

/-- Publication-facing wrapper for the factorization core of `prop:sync-kernel-spectrum`
in the self-dual and ETDS kernel papers. -/
theorem paper_sync_kernel_spectrum_seeds :
    (∀ w : ℤ, syncPolyS2 w = syncPolyS2_factored w) ∧
    syncPolyS2 1 = 0 ∧
    syncPolyS2 (-1) = 0 ∧
    ((3 : ℤ)^6 - 2 * 3^5 - 5 * 3^4 + 6 * 3^3 + 3^2 - 4 * 3 + 3 = 0) := by
  exact ⟨syncPolyS2_eq_factored, syncPolyS2_root_1, syncPolyS2_root_neg1,
    syncPolyS2_root_third_scaled⟩

end Omega.Zeta
