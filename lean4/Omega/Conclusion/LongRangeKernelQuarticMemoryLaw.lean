import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-long-range-kernel-quartic-memory-law`. -/
theorem paper_conclusion_long_range_kernel_quartic_memory_law
    (kernelAsymptotic loopEntropyChainScaling quarticMemoryLaw : Prop)
    (hKernel : kernelAsymptotic)
    (hScale : kernelAsymptotic → loopEntropyChainScaling)
    (hQuartic : loopEntropyChainScaling → quarticMemoryLaw) :
    kernelAsymptotic ∧ loopEntropyChainScaling ∧ quarticMemoryLaw := by
  exact ⟨hKernel, hScale hKernel, hQuartic (hScale hKernel)⟩

end Omega.Conclusion
