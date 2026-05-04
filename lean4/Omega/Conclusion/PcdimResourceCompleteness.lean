import Omega.Conclusion.PcdimMaxLaw

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-pcdim-resource-completeness`.
For a finite prime support, the resource threshold is exactly the supremum of the prime profile. -/
theorem paper_conclusion_pcdim_resource_completeness (P : Finset Nat) (dp : Nat -> Nat)
    (r pcdimK : Nat) (connectedTorusExtensionExists : Prop)
    (hPcdim : pcdimK = P.sup dp)
    (hThreshold : connectedTorusExtensionExists ↔ ∀ p ∈ P, dp p ≤ r) :
    connectedTorusExtensionExists ↔ pcdimK ≤ r := by
  rw [hThreshold, hPcdim]
  exact (Finset.sup_le_iff (s := P) (f := dp) (a := r)).symm

end Omega.Conclusion
