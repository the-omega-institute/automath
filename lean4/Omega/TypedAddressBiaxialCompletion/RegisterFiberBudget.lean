namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing wrapper for the four register-axis consequences of a fixed local rank: exact
finite-layer selector size, the `ℤ_p^r`-torsor inverse limit, multiplicative finite-prime readout
budget, and the adelic envelope.
    prop:typed-address-biaxial-completion-register-fiber-budget -/
theorem paper_typed_address_biaxial_completion_register_fiber_budget
    (localRank layerSelectorSize inverseLimitTorsor finitePrimeReadoutSize adelicEnvelope : Prop)
    (hLayer : localRank -> layerSelectorSize)
    (hLimit : localRank -> inverseLimitTorsor)
    (hFinite : localRank -> finitePrimeReadoutSize)
    (hAdelic : localRank -> adelicEnvelope)
    (hRank : localRank) :
    layerSelectorSize ∧ inverseLimitTorsor ∧ finitePrimeReadoutSize ∧ adelicEnvelope := by
  exact ⟨hLayer hRank, hLimit hRank, hFinite hRank, hAdelic hRank⟩

end Omega.TypedAddressBiaxialCompletion
