import Omega.Zeta.XiRootUnityFilterSingleClassInjection

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-length2-atomic-root-unity-singleclass-injection`. -/
theorem paper_conclusion_length2_atomic_root_unity_singleclass_injection
    (q a : Nat) (hq : 2 <= q)
    (primitivePeeling rootUnityOrthogonality primitiveLocalized periodicLogLocalized : Prop)
    (hPeeling : primitivePeeling)
    (hRoot : primitivePeeling -> rootUnityOrthogonality)
    (hPrimitive : rootUnityOrthogonality -> primitiveLocalized)
    (hPeriodic : rootUnityOrthogonality -> periodicLogLocalized) :
    primitiveLocalized ∧ periodicLogLocalized := by
  exact Omega.Zeta.paper_xi_root_unity_filter_single_class_injection q a hq
    primitivePeeling rootUnityOrthogonality primitiveLocalized periodicLogLocalized
    hPeeling hRoot hPrimitive hPeriodic

end Omega.Conclusion
