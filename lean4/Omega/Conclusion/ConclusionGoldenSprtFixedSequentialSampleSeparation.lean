namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-golden-sprt-fixed-sequential-sample-separation`. -/
theorem paper_conclusion_golden_sprt_fixed_sequential_sample_separation
    (fixed_window_asymptotic sequential_window_asymptotic golden_ratio_limit : Prop)
    (hFix : fixed_window_asymptotic) (hSeq : sequential_window_asymptotic)
    (hLimit : fixed_window_asymptotic -> sequential_window_asymptotic -> golden_ratio_limit) :
    golden_ratio_limit := by
  exact hLimit hFix hSeq

end Omega.Conclusion
