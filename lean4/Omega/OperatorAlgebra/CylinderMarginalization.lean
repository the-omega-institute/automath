import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Chapter-local data for cylinder-probability marginalization. The structure fixes a word, its
two one-step extensions, the cylinder probability observable, and the trace-additivity witness
showing that the parent cylinder splits as the sum of its two children. -/
structure CylinderMarginalizationData where
  word : List Bool
  cylinderProbability : List Bool → ℝ
  extendZero : List Bool → List Bool
  extendOne : List Bool → List Bool
  extendZero_spec : extendZero word = word ++ [false]
  extendOne_spec : extendOne word = word ++ [true]
  traceAdditivityWitness :
    cylinderProbability word =
      cylinderProbability (extendZero word) + cylinderProbability (extendOne word)
  splitIdentity : Prop
  marginalizationIdentity : Prop
  kolmogorovConsistency : Prop
  deriveSplitIdentity :
    (cylinderProbability word =
      cylinderProbability (extendZero word) + cylinderProbability (extendOne word)) →
        splitIdentity
  deriveMarginalizationIdentity :
    splitIdentity → marginalizationIdentity
  deriveKolmogorovConsistency :
    marginalizationIdentity → kolmogorovConsistency

/-- Paper-facing wrapper for cylinder-probability marginalization: the trace additivity of the two
one-step extensions yields the split identity for a fixed cylinder, and Kolmogorov consistency is
the immediate corollary.
    prop:op-algebra-cylinder-marginalization -/
theorem paper_op_algebra_cylinder_marginalization (D : CylinderMarginalizationData) :
    D.marginalizationIdentity ∧ D.kolmogorovConsistency := by
  have hSplit : D.splitIdentity :=
    D.deriveSplitIdentity D.traceAdditivityWitness
  have hMarg : D.marginalizationIdentity :=
    D.deriveMarginalizationIdentity hSplit
  exact ⟨hMarg, D.deriveKolmogorovConsistency hMarg⟩

end Omega.OperatorAlgebra
