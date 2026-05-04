import Omega.Conclusion.SmithPKernelSpectrumConeSimplicial

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-smith-p-kernel-spectrum-free-commutative-monoid`. -/
theorem paper_conclusion_smith_p_kernel_spectrum_free_commutative_monoid
    (D : SmithPKernelSpectrumConeSimplicialData) :
    D.freeCommutativeMonoidModel ∧ D.atomicExtremeRays := by
  exact ⟨(paper_conclusion_smith_p_kernel_spectrum_cone_simplicial D).1,
    (paper_conclusion_smith_p_kernel_spectrum_cone_simplicial D).2.2⟩

end Omega.Conclusion
