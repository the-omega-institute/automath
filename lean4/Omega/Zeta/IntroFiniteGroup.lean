namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the ETDS introduction theorem on primitive determinant calculus for
    finite-group extensions. The theorem packages the Adams--Möbius inversion layer, the
    Chebotarev/Mertens/Fourier reconstruction layer, the quotient-functoriality shadow layer,
    and the explicit `S_3` counterexample to naive primitive-bias vanishing.
    thm:intro-finite-group -/
theorem paper_etds_intro_finite_group
    {System Group : Type}
    (adamsMobiusPackage : System → Group → Prop)
    (chebotarevMertensFourierPackage : System → Group → Prop)
    (quotientShadowPackage : System → Group → Prop)
    (signCharacterCounterexample : System → Group → Prop)
    {A : System} {G : Group}
    (hAdamsMobius : adamsMobiusPackage A G)
    (hChebotarev : chebotarevMertensFourierPackage A G)
    (hQuotient : quotientShadowPackage A G)
    (hCounterexample : signCharacterCounterexample A G) :
    adamsMobiusPackage A G ∧
      chebotarevMertensFourierPackage A G ∧
      quotientShadowPackage A G ∧
      signCharacterCounterexample A G := by
  exact ⟨hAdamsMobius, hChebotarev, hQuotient, hCounterexample⟩

end Omega.Zeta
