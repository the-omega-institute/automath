namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-ramanujan-kernel-psd-derivative-parseval-control`. -/
theorem paper_conclusion_ramanujan_kernel_psd_derivative_parseval_control
    (linearExpansion derivativeParseval cauchySchwarzControl ramanujanKernelPsd : Prop)
    (hExpansion : linearExpansion)
    (hParseval : derivativeParseval)
    (hControl : linearExpansion → derivativeParseval → cauchySchwarzControl)
    (hPsd : cauchySchwarzControl → ramanujanKernelPsd) :
    linearExpansion ∧ derivativeParseval ∧ cauchySchwarzControl ∧ ramanujanKernelPsd := by
  exact ⟨hExpansion, hParseval, hControl hExpansion hParseval,
    hPsd (hControl hExpansion hParseval)⟩

end Omega.Conclusion
