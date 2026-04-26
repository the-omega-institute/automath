import Omega.TypedAddressBiaxialCompletion.ComovingPronyThreshold

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-toeplitz-defect-exact-nyquist-threshold`. This is the
Conclusion-level restatement of the typed-address comoving Prony threshold split. -/
theorem paper_conclusion_toeplitz_defect_exact_nyquist_threshold
    (D : Omega.TypedAddressBiaxialCompletion.ComovingPronyThresholdData) :
    D.rankDetectionWindow = 2 * D.kappa - 1 ∧ D.exactRecoveryWindow = 2 * D.kappa := by
  simpa using
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_prony_threshold
      D

end Omega.Conclusion
