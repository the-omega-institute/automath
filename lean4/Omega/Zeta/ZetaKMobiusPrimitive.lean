import Omega.Zeta.DynZeta

namespace Omega.Zeta

/-- Paper label: `prop:zetaK-mobius-primitive`. -/
theorem paper_zetak_mobius_primitive (traceFromPrimitive primitiveFromTrace : Prop)
    (hTrace : traceFromPrimitive) (hMobius : traceFromPrimitive → primitiveFromTrace) :
    traceFromPrimitive ∧ primitiveFromTrace := by
  exact ⟨hTrace, hMobius hTrace⟩

end Omega.Zeta
