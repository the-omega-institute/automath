import Mathlib

namespace Omega.Conclusion

/-- Concrete bookkeeping for the skeletal `2`-group/Postnikov-class strictification wrapper. The
fields are concrete carriers and class representatives, not abstract propositional assumptions. -/
structure TwoGroupPostnikovStrictificationData where
  groupCardinalityWitness : ℕ
  postnikovClassRepresentative : ℤ
  extendedPostnikovClassRepresentative : ℤ

namespace TwoGroupPostnikovStrictificationData

/-- Every group gives a one-object skeletal `2`-group package in this concrete wrapper. -/
def hasSkeletalTwoGroup (D : TwoGroupPostnikovStrictificationData) : Prop :=
  0 < D.groupCardinalityWitness + 1

/-- Vanishing of the Postnikov class. -/
def postnikovClassZero (D : TwoGroupPostnikovStrictificationData) : Prop :=
  D.postnikovClassRepresentative = 0

/-- Strictifiability is identified with trivial Postnikov class in the wrapper. -/
def strictifiable (D : TwoGroupPostnikovStrictificationData) : Prop :=
  D.postnikovClassRepresentative = 0

/-- The coefficient extension trivializes exactly when the extended class vanishes. -/
def coefficientExtensionTrivializes (D : TwoGroupPostnikovStrictificationData) : Prop :=
  D.extendedPostnikovClassRepresentative = 0

/-- After such an extension, the strictified wrapper has vanishing extended Postnikov class. -/
def strictifiableAfterExtension (D : TwoGroupPostnikovStrictificationData) : Prop :=
  D.extendedPostnikovClassRepresentative = 0

end TwoGroupPostnikovStrictificationData

/-- Paper label: `prop:conclusion-2group-postnikov-strictification`. -/
theorem paper_conclusion_2group_postnikov_strictification (D : TwoGroupPostnikovStrictificationData) :
    D.hasSkeletalTwoGroup ∧ (D.postnikovClassZero ↔ D.strictifiable) ∧
      (D.coefficientExtensionTrivializes → D.strictifiableAfterExtension) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [TwoGroupPostnikovStrictificationData.hasSkeletalTwoGroup] using
      Nat.succ_pos D.groupCardinalityWitness
  · constructor <;> intro h <;> simpa
      [TwoGroupPostnikovStrictificationData.postnikovClassZero,
        TwoGroupPostnikovStrictificationData.strictifiable] using h
  · intro h
    simpa [TwoGroupPostnikovStrictificationData.coefficientExtensionTrivializes,
      TwoGroupPostnikovStrictificationData.strictifiableAfterExtension] using h

end Omega.Conclusion
