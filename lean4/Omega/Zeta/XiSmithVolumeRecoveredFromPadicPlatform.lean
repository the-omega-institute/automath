import Omega.Zeta.SmithEntropyMinDepth

namespace Omega.Zeta

/-- Paper label: `cor:xi-smith-volume-recovered-from-padic-platform`. -/
theorem paper_xi_smith_volume_recovered_from_padic_platform (s : Multiset ℕ) (K : ℕ)
    (hK : ∀ v ∈ s, v ≤ K) :
    ∀ k : ℕ, K ≤ k → Omega.Zeta.smithEntropy s k = s.sum := by
  intro k hk
  exact smithEntropy_eq_sum_of_all_le s k (fun v hv => le_trans (hK v hv) hk)

end Omega.Zeta
