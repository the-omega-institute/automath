import Omega.POM.A4TracePrimitiveTwoTerm

namespace Omega.POM

/-- Pushing the two-term primitive-orbit expansion through a linear observable preserves the
leading Perron contribution and the alternating subleading correction after normalization.
    cor:pom-a4-linear-observable-two-term-oscillation -/
theorem paper_pom_a4_linear_observable_two_term_oscillation
    (D : A4TracePrimitiveTwoTermData)
    (linearObservableTwoTermExpansion normalizedOscillation alternatingCorrection : Prop)
    (h : D.primitiveOrbitTwoTermExpansion → D.alternatingSubleadingSign →
      linearObservableTwoTermExpansion ∧ normalizedOscillation ∧ alternatingCorrection) :
    linearObservableTwoTermExpansion ∧ normalizedOscillation ∧ alternatingCorrection := by
  have hPackage := paper_pom_a4_trace_primitive_two_term D
  exact h hPackage.2.2.2.2.2.1 hPackage.2.2.2.2.2.2

end Omega.POM
