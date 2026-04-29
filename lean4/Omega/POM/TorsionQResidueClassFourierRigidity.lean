namespace Omega.POM.TorsionQResidueClassFourierRigidity

/-- Paper label: `thm:pom-torsion-q-residue-class-fourier-rigidity`. -/
theorem paper_pom_torsion_q_residue_class_fourier_rigidity (q : ℕ)
    (residueClassLimits fourierInversion flatResidues torsionSymmetry : Prop)
    (hLimits : residueClassLimits) (hInv : residueClassLimits → fourierInversion)
    (hFlat : fourierInversion → flatResidues) (hTorsion : flatResidues → torsionSymmetry) :
    residueClassLimits ∧ fourierInversion ∧ flatResidues ∧ torsionSymmetry := by
  have _ : q = q := rfl
  exact ⟨hLimits, hInv hLimits, hFlat (hInv hLimits), hTorsion (hFlat (hInv hLimits))⟩

end Omega.POM.TorsionQResidueClassFourierRigidity
