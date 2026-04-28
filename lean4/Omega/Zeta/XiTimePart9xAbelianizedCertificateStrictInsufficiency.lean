import Omega.Zeta.XiTimePart9xNonabelianArtinChannelQuotientErasure

namespace Omega.Zeta

/-- Abelianization-specialized Artin erasure data.  The channel predicates record that inflated
abelian characters are precisely the one-dimensional channels, while the transfer rule applies
the nonabelian quotient-erasure theorem to any surviving higher-dimensional factor. -/
structure xi_time_part9x_abelianized_certificate_strict_insufficiency_data where
  inflatedAbelianCharacter : ℕ → Prop
  oneDimensionalArtinChannel : ℕ → Prop
  hasNontrivialHigherDimensionalArtinFactor : Prop
  abelianizedLabelsIncomplete : Prop
  twistedPrimitiveOrbitLawIncomplete : Prop
  inflated_abelian_characters_exactly_one_dimensional :
    ∀ ρ : ℕ, inflatedAbelianCharacter ρ ↔ oneDimensionalArtinChannel ρ
  abelianized_insufficiency_from_nonabelian_erasure :
    ((∀ m t u v,
        Omega.EA.kernelArtinDetFactorization m t u v ∧
          Omega.EA.kernelArtinZetaFactorization t u v) ∧
      Omega.Zeta.paper_xi_time_part64_nonabelian_quotient_energy_loss_exact) →
      (∀ ρ : ℕ, inflatedAbelianCharacter ρ ↔ oneDimensionalArtinChannel ρ) →
        hasNontrivialHigherDimensionalArtinFactor →
          abelianizedLabelsIncomplete ∧ twistedPrimitiveOrbitLawIncomplete

/-- Paper label:
`cor:xi-time-part9x-abelianized-certificate-strict-insufficiency`. -/
theorem paper_xi_time_part9x_abelianized_certificate_strict_insufficiency
    (D : xi_time_part9x_abelianized_certificate_strict_insufficiency_data) :
    D.hasNontrivialHigherDimensionalArtinFactor →
      D.abelianizedLabelsIncomplete ∧ D.twistedPrimitiveOrbitLawIncomplete := by
  intro hHigher
  exact D.abelianized_insufficiency_from_nonabelian_erasure
    Omega.Zeta.paper_xi_time_part9x_nonabelian_artin_channel_quotient_erasure
    D.inflated_abelian_characters_exactly_one_dimensional hHigher

end Omega.Zeta
