namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-underresolution-two-atomic-curvature-measure`. -/
theorem paper_xi_foldbin_underresolution_two_atomic_curvature_measure
    (tailLimit capacityLimit curvatureAtoms tailIntegralIdentity tailTailIdentity : Prop)
    (hTail : tailLimit) (hCapacity : capacityLimit)
    (hCurv : tailLimit -> capacityLimit -> curvatureAtoms)
    (hIntegral : curvatureAtoms -> tailIntegralIdentity)
    (hTailId : curvatureAtoms -> tailTailIdentity) :
    curvatureAtoms ∧ tailIntegralIdentity ∧ tailTailIdentity := by
  let hAtoms : curvatureAtoms := hCurv hTail hCapacity
  exact ⟨hAtoms, hIntegral hAtoms, hTailId hAtoms⟩

end Omega.Zeta
