namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-angular-prony-stability`. -/
theorem paper_conclusion_angular_prony_stability
    (hankelInvertible smallNoise simpleRoots vandermondeRecoverable pronyInverseExists
      localLipschitzBound : Prop)
    (hLinearStep : hankelInvertible → smallNoise → simpleRoots)
    (hRootStep : simpleRoots → vandermondeRecoverable)
    (hWeightStep : vandermondeRecoverable → pronyInverseExists ∧ localLipschitzBound) :
    hankelInvertible → smallNoise → pronyInverseExists ∧ localLipschitzBound := by
  intro hHankel hNoise
  exact hWeightStep (hRootStep (hLinearStep hHankel hNoise))

end Omega.Conclusion
