import Omega.Zeta.XiOfflineMembershipGrassmannLowerBound
import Mathlib.Tactic

namespace Omega.Zeta

/-- Number of free field entries in a row-reduced representative of a codimension-`r` subspace. -/
def xi_offline_membership_near_optimal_encoding_free_entries (n r : ℕ) : ℕ :=
  r * (n - r)

/-- A concrete pivot-position overhead budget: each of `n` positions is encoded using `log2(n+1)`
bits. -/
def xi_offline_membership_near_optimal_encoding_pivot_overhead (n : ℕ) : ℕ :=
  n * Nat.log2 (n + 1)

/-- Main field-entry storage cost for the canonical row-reduced encoding. -/
def xi_offline_membership_near_optimal_encoding_main_bits (pBits n r : ℕ) : ℕ :=
  xi_offline_membership_near_optimal_encoding_free_entries n r * pBits

/-- Canonical row-reduced encoding length: free entries plus pivot-position overhead. -/
def xi_offline_membership_near_optimal_encoding_canonical_bits
    (pBits n r : ℕ) : ℕ :=
  xi_offline_membership_near_optimal_encoding_main_bits pBits n r +
    xi_offline_membership_near_optimal_encoding_pivot_overhead n

/-- Paper label: `cor:xi-offline-membership-near-optimal-encoding`. -/
theorem paper_xi_offline_membership_near_optimal_encoding
    (p n r lowerEll grassmannCard pBits : ℕ)
    (hr : r ≤ n)
    (hGrassmann :
      p ^ xi_offline_membership_near_optimal_encoding_free_entries n r ≤ grassmannCard)
    (hencode : ∃ encode : Fin grassmannCard → Fin (2 ^ lowerEll), Function.Injective encode) :
    p ^ xi_offline_membership_near_optimal_encoding_free_entries n r ≤ 2 ^ lowerEll ∧
      xi_offline_membership_near_optimal_encoding_canonical_bits pBits n r =
        xi_offline_membership_near_optimal_encoding_main_bits pBits n r +
          xi_offline_membership_near_optimal_encoding_pivot_overhead n ∧
      xi_offline_membership_near_optimal_encoding_main_bits pBits n r ≤
        xi_offline_membership_near_optimal_encoding_canonical_bits pBits n r := by
  refine ⟨?_, ?_, ?_⟩
  · exact paper_xi_offline_membership_grassmann_lower_bound p n r lowerEll grassmannCard hr
      hGrassmann hencode
  · rfl
  · simp [xi_offline_membership_near_optimal_encoding_canonical_bits]

end Omega.Zeta
