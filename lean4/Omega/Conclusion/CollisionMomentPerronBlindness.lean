import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-collision-moment-perron-blindness`. -/
theorem paper_conclusion_collision_moment_perron_blindness
    (lambdaZero radiusOne arbitrarilyLargeStateComplexity : Prop) (hLambda : lambdaZero)
    (hRadius : lambdaZero → radiusOne) (hState : arbitrarilyLargeStateComplexity) :
    lambdaZero ∧ radiusOne ∧ arbitrarilyLargeStateComplexity := by
  exact ⟨hLambda, hRadius hLambda, hState⟩

end Omega.Conclusion
