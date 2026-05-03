import Omega.CircleDimension.LocalizedGsEmbeddingOrder

namespace Omega.Conclusion

/-- Finite-prime localizations have the compatible quotient on dual solenoids and the
discrete-side embedding exactly in the inclusion order on prime supports.
    thm:conclusion-finite-primesupport-quotient-order-characterization -/
theorem paper_conclusion_finite_primesupport_quotient_order_characterization
    (D : Omega.CircleDimension.LocalizedGsEmbeddingOrderData) :
    (D.S ⊆ D.T) ↔
      Omega.CircleDimension.LocalizedGsEmbeddingOrderData.compatibleDualSurjection D.S D.T ∧
        Omega.CircleDimension.LocalizedGsEmbeddingOrderData.localizedEmbedding D.S D.T := by
  classical
  have hPackage := Omega.CircleDimension.paper_cdim_localized_gs_embedding_order D
  constructor
  · intro hST
    exact ⟨hPackage.2.2 hST, hPackage.1.2 hST⟩
  · rintro ⟨_hDual, hEmbedding⟩
    exact hPackage.1.1 hEmbedding

end Omega.Conclusion
