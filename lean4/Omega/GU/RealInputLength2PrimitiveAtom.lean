import Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBound

namespace Omega.GU

/-- Paper-facing extraction of the length-two primitive atom from the real-input weighted zeta
package, together with the induced ghost-trace contribution.
    thm:gut-real-input-length2-primitive-atom -/
theorem paper_gut_real_input_length2_primitive_atom
    (D : Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBoundData)
    (primitiveLengthTwoAtom ghostTraceContribution : Prop)
    (hPrimitive : D.primitiveCycleDensityBound → D.lengthTwoSharpWitness → primitiveLengthTwoAtom)
    (hGhost : primitiveLengthTwoAtom → ghostTraceContribution) :
    primitiveLengthTwoAtom ∧ ghostTraceContribution := by
  rcases Omega.SyncKernelWeighted.paper_real_input_40_arity_charge_density_bound D with
    ⟨hBound, hWitness⟩
  have hAtom : primitiveLengthTwoAtom := hPrimitive hBound hWitness
  exact ⟨hAtom, hGhost hAtom⟩

end Omega.GU
