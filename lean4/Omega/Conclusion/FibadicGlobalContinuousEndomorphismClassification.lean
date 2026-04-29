import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fibadic-global-continuous-endomorphism-classification`.
The scalar attached to `T` is `toScalar T`; pointwise scalar action follows from `h_act`, and
uniqueness is discharged by `h_unique`. -/
theorem paper_conclusion_fibadic_global_continuous_endomorphism_classification
    (X Alpha End : Type*) (acts : End → X → X) (scalarAct : Alpha → X → X)
    (toScalar : End → Alpha)
    (h_act : ∀ T x, acts T x = scalarAct (toScalar T) x)
    (h_unique : ∀ T a, (∀ x, acts T x = scalarAct a x) → a = toScalar T) :
    ∀ T, ∃! a, ∀ x, acts T x = scalarAct a x := by
  intro T
  refine ⟨toScalar T, ?_, ?_⟩
  · intro x
    exact h_act T x
  · intro a ha
    exact h_unique T a ha

end Omega.Conclusion
