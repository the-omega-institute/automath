namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-comoving-algebraic-vs-numerical-identifiability-split`. -/
theorem paper_conclusion_comoving_algebraic_vs_numerical_identifiability_split
    (kappa : Nat) (hkappa : 2 <= kappa)
    (algebraicallyIdentifiable uniformlyLipschitzStable strictSeparation : Prop)
    (hAlg : algebraicallyIdentifiable)
    (hNoStable : uniformlyLipschitzStable -> False)
    (hSplit : algebraicallyIdentifiable -> (uniformlyLipschitzStable -> False) ->
      strictSeparation) :
    algebraicallyIdentifiable ∧ ¬ uniformlyLipschitzStable ∧ strictSeparation := by
  have _hkappa : 2 <= kappa := hkappa
  exact ⟨hAlg, hNoStable, hSplit hAlg hNoStable⟩

end Omega.Conclusion
