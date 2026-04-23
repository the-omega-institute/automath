import Omega.Conclusion.SublinearExcitationFilterInsufficient

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-kernel-rh-only-finitely-often-on-fixed-ray`. -/
theorem paper_conclusion_kernel_rh_only_finitely_often_on_fixed_ray
    (a : ℕ) (rho eta c : ℝ) (hRho : 1 < rho) (hEta0 : 0 < eta) (hEtaLt : eta < rho)
    (k : ℕ → ℝ) (kernelRH : ℕ → Prop)
    (hSubcritical : c < criticalExcitationSlope rho eta)
    (hEventuallyUpper : ∃ N : ℕ, ∀ b ≥ N, k b ≤ c * b)
    (hNecessaryLower :
      ∀ b, 2 ≤ b → kernelRH (a * b) → criticalExcitationSlope rho eta * b ≤ k b) :
    ∃ N : ℕ, ∀ b ≥ N, ¬ kernelRH (a * b) := by
  let D : SublinearExcitationFilterData :=
    { rho := rho
      eta := eta
      hRho := hRho
      hEta0 := hEta0
      hEtaLt := hEtaLt
      k := k
      kernelRH := fun b => kernelRH (a * b)
      c := c
      hSubcritical := hSubcritical
      hEventuallyUpper := hEventuallyUpper
      hNecessaryLower := hNecessaryLower }
  simpa [D, SublinearExcitationFilterData.sublinearFiltersFailEventually] using
    paper_conclusion_sublinear_excitation_filter_insufficient D

end Omega.Conclusion
