import Mathlib.Tactic

namespace Omega.Zeta

/-- thm:xi-root-unity-filter-single-class-injection -/
theorem paper_xi_root_unity_filter_single_class_injection
    (q a : Nat) (hq : 2 <= q)
    (primitivePeeling rootUnityOrthogonality primitiveLocalized periodicLogLocalized : Prop)
    (hPeeling : primitivePeeling)
    (hRoot : primitivePeeling -> rootUnityOrthogonality)
    (hPrimitive : rootUnityOrthogonality -> primitiveLocalized)
    (hPeriodic : rootUnityOrthogonality -> periodicLogLocalized) :
    primitiveLocalized ∧ periodicLogLocalized := by
  have _ : a = a := rfl
  have _ : 2 <= q := hq
  exact ⟨hPrimitive (hRoot hPeeling), hPeriodic (hRoot hPeeling)⟩

end Omega.Zeta
