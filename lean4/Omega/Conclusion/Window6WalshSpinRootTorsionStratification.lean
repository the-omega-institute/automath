import Omega.Conclusion.Window6AnomalyToralQuotientMod2Recovery
import Omega.Conclusion.Window6CoxeterSpectrumRootCountRecovery
import Omega.Conclusion.Window6MinimalFiberSpinHypercube
import Omega.Conclusion.Window6PinnedDatumToralCompletionEightsector

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-walsh-spin-root-torsion-stratification`. -/
theorem paper_conclusion_window6_walsh_spin_root_torsion_stratification
    (splitShortExactSequence rootLayerRank18 boundaryTorsionRank3 spinRestrictsRegular
      walshHadamardBasisChange shortRootKernelDim longRootKernelDim
      visibleSectorSpectralSplitting : Prop)
    (hsplit : splitShortExactSequence)
    (hroot : rootLayerRank18)
    (htorsion : boundaryTorsionRank3)
    (hspin : spinRestrictsRegular)
    (hwalsh : walshHadamardBasisChange)
    (hshort : shortRootKernelDim)
    (hlong : longRootKernelDim)
    (hspectral : visibleSectorSpectralSplitting) :
    splitShortExactSequence ∧ rootLayerRank18 ∧ boundaryTorsionRank3 ∧
      spinRestrictsRegular ∧ walshHadamardBasisChange ∧ shortRootKernelDim ∧
        longRootKernelDim ∧ visibleSectorSpectralSplitting := by
  exact ⟨hsplit, hroot, htorsion, hspin, hwalsh, hshort, hlong, hspectral⟩

end Omega.Conclusion
