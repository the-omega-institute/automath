import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fixed-resolution-hankel-finite-determinacy-multiplicity-spectrum`. -/
theorem paper_conclusion_fixed_resolution_hankel_finite_determinacy_multiplicity_spectrum
    (rankEqualsSupport allLargeHankelMinorsVanish positivePrincipalMinor
      finiteMomentRecovery : Prop)
    (hfactor : rankEqualsSupport ∧ allLargeHankelMinorsVanish ∧ positivePrincipalMinor)
    (hrecover : rankEqualsSupport → positivePrincipalMinor → finiteMomentRecovery) :
    rankEqualsSupport ∧ allLargeHankelMinorsVanish ∧ positivePrincipalMinor ∧
      finiteMomentRecovery := by
  rcases hfactor with ⟨hrank, hminors, hpositive⟩
  exact ⟨hrank, hminors, hpositive, hrecover hrank hpositive⟩

end Omega.Conclusion
