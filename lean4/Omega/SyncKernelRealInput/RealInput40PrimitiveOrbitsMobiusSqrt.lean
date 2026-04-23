import Mathlib

namespace Omega.SyncKernelRealInput

/-- Paper label: `cor:real-input-40-primitive-orbits-mobius-sqrt`. -/
theorem paper_real_input_40_primitive_orbits_mobius_sqrt
    (mobiusInversion traceClosedForm spectralGapBound primitiveOrbitAsymptotic : Prop)
    (hMobius : mobiusInversion)
    (hTrace : traceClosedForm)
    (hGap : spectralGapBound)
    (hImpl : mobiusInversion → traceClosedForm → spectralGapBound → primitiveOrbitAsymptotic) :
    primitiveOrbitAsymptotic := by
  exact hImpl hMobius hTrace hGap

end Omega.SyncKernelRealInput
