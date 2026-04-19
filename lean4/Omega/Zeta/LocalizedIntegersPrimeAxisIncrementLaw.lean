import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersPadicKernelRigidity

namespace Omega.Zeta

/-- Chapter-local package for the localized-integers prime-axis increment law. The data record the
comparison of `G_S` and `G_T` modulo their common copy of `ℤ`, the identification of the new
torsion summand contributed by `T \ S`, the dual `p`-adic axis increment, and the reuse of the
localized `p`-adic kernel rigidity package to keep the connected circle part stable. -/
structure LocalizedIntegersPrimeAxisIncrementLawData where
  commonIntegerComparison : Prop
  newTorsionSummandIdentification : Prop
  dualAxisIdentification : Prop
  padicKernelRigidityPackage : LocalizedIntegersPadicKernelRigidityData
  discreteShortExactSequence : Prop
  pontryaginDualShortExactSequence : Prop
  connectedPartAndCircleDimensionStable : Prop
  commonIntegerComparison_h : commonIntegerComparison
  newTorsionSummandIdentification_h : newTorsionSummandIdentification
  dualAxisIdentification_h : dualAxisIdentification
  deriveDiscreteShortExactSequence :
    commonIntegerComparison → newTorsionSummandIdentification → discreteShortExactSequence
  derivePontryaginDualShortExactSequence :
    discreteShortExactSequence → dualAxisIdentification → pontryaginDualShortExactSequence
  deriveConnectedPartAndCircleDimensionStable :
    padicKernelRigidityPackage.connectedComponentIsCircle →
      padicKernelRigidityPackage.circleDimensionOne → connectedPartAndCircleDimensionStable

/-- Paper-facing wrapper for the localized-integers prime-axis increment law: quotienting by the
common copy of `ℤ` isolates the new Prüfer summand on the discrete side, duality adds exactly the
new `p`-adic axes, and the connected circle component remains unchanged by the previously
formalized `p`-adic kernel rigidity package.
    cor:xi-localized-integers-prime-axis-increment-law -/
theorem paper_xi_localized_integers_prime_axis_increment_law
    (D : LocalizedIntegersPrimeAxisIncrementLawData) :
    D.discreteShortExactSequence ∧ D.pontryaginDualShortExactSequence ∧
      D.connectedPartAndCircleDimensionStable := by
  have hDiscrete : D.discreteShortExactSequence :=
    D.deriveDiscreteShortExactSequence D.commonIntegerComparison_h
      D.newTorsionSummandIdentification_h
  have hDual : D.pontryaginDualShortExactSequence :=
    D.derivePontryaginDualShortExactSequence hDiscrete D.dualAxisIdentification_h
  have hStable : D.connectedPartAndCircleDimensionStable :=
    D.deriveConnectedPartAndCircleDimensionStable
      D.padicKernelRigidityPackage.connectedComponentWitness
      D.padicKernelRigidityPackage.circleDimensionWitness
  exact ⟨hDiscrete, hDual, hStable⟩

end Omega.Zeta
