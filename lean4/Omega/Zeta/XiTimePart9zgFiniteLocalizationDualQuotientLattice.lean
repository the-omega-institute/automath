import Omega.CircleDimension.LocalizedGsEmbeddingOrder

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zg-finite-localization-dual-quotient-lattice`. Reversing the
finite prime supports records the contravariant Pontryagin-dual quotient direction. -/
theorem paper_xi_time_part9zg_finite_localization_dual_quotient_lattice
    (D : Omega.CircleDimension.LocalizedGsEmbeddingOrderData) :
    (Omega.CircleDimension.LocalizedGsEmbeddingOrderData.localizedEmbedding D.T D.S ↔
      D.T ⊆ D.S) ∧
      (Omega.CircleDimension.LocalizedGsEmbeddingOrderData.compatibleDualSurjection D.T D.S ↔
        D.T ⊆ D.S) := by
  let Drev : Omega.CircleDimension.LocalizedGsEmbeddingOrderData :=
    { S := D.T
      T := D.S
      S_primes := D.T_primes
      T_primes := D.S_primes }
  simpa [Drev, Omega.CircleDimension.LocalizedGsEmbeddingOrderData.package] using
    Omega.CircleDimension.paper_cdim_localized_gs_embedding_order Drev

end Omega.Zeta
