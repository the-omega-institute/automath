import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-two-endpoint-incompatible-finite-determinacy`. -/
theorem paper_conclusion_two_endpoint_incompatible_finite_determinacy
    (J : ℕ) (hJ : 2 ≤ J) (Dist : Type) (fullSupport : Dist → Prop)
    (sameIntegerMoments : ℕ → Dist → Dist → Prop)
    (sameZeroRateJet : ℕ → Dist → Dist → Prop)
    (halfEndpointDifferent : Dist → Dist → Prop)
    (hMomentWitness :
      ∀ Q, 2 ≤ Q → ∃ w wtilde : Dist,
        fullSupport w ∧ fullSupport wtilde ∧ sameIntegerMoments Q w wtilde ∧
          halfEndpointDifferent w wtilde)
    (hJet :
      ∀ w wtilde, sameIntegerMoments (J + 1) w wtilde → sameZeroRateJet J w wtilde) :
    ∃ w wtilde : Dist,
      fullSupport w ∧ fullSupport wtilde ∧ sameIntegerMoments (J + 1) w wtilde ∧
        sameZeroRateJet J w wtilde ∧ halfEndpointDifferent w wtilde := by
  have hQ : 2 ≤ J + 1 := by omega
  rcases hMomentWitness (J + 1) hQ with
    ⟨w, wtilde, hw, hwtilde, hsame, hhalf⟩
  exact ⟨w, wtilde, hw, hwtilde, hsame, hJet w wtilde hsame, hhalf⟩

end Omega.Conclusion
