import Mathlib

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-cycle-lattice-determinant-extensivity`. -/
theorem paper_conclusion_cycle_lattice_determinant_extensivity
    (directSumCounting affineCosetCounting determinantCorrectionAdditive
      notRegionEntanglement : Prop)
    (hmain : directSumCounting) (haffine : affineCosetCounting)
    (hadd : directSumCounting → determinantCorrectionAdditive)
    (hrt : determinantCorrectionAdditive → notRegionEntanglement) :
    directSumCounting ∧ affineCosetCounting ∧ determinantCorrectionAdditive ∧
      notRegionEntanglement := by
  exact ⟨hmain, haffine, hadd hmain, hrt (hadd hmain)⟩

end Omega.Conclusion
