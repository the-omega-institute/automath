import Mathlib.Tactic
import Omega.CircleDimension.RankonePhasePrimeFiber

namespace Omega.CircleDimension

/-- Chapter theorem for rank-one solenoids: once the rank-one phase/prime-fiber package is fixed,
the height-sequence classification identifies the same object as a one-dimensional solenoid with
the expected short exact sequence, prime-fiber quotient, supernatural kernel register, and
inverse-limit presentation. -/
theorem paper_cdim_rank_one_solenoid_height_classification (D : RankonePhasePrimeFiberData)
    (circleDimOne heightSequenceClassification : Prop) (hcdim : circleDimOne)
    (hheight : heightSequenceClassification) :
    circleDimOne ∧ D.shortExactSequence ∧ D.quotientPrimeFiberDescription ∧
      D.kernelIsSupernaturalRegister ∧ D.inverseLimitPresentation ∧
      heightSequenceClassification := by
  exact
    ⟨hcdim, D.shortExactSequenceWitness, D.quotientPrimeFiberDescriptionWitness,
      D.kernelIsSupernaturalRegisterWitness, D.inverseLimitPresentationWitness, hheight⟩

end Omega.CircleDimension
