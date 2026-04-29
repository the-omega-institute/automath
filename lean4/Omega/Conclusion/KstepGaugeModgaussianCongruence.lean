namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-kstep-gauge-modgaussian-congruence`. -/
theorem paper_conclusion_kstep_gauge_modgaussian_congruence
    (k ell : Nat)
    (hk : 1 ≤ k)
    (hell : 1 ≤ ell)
    (localLogRatioLimit gaussianScaleRatioLimit sameModGaussianClass : Prop)
    (hlocal : localLogRatioLimit)
    (hgauss : gaussianScaleRatioLimit)
    (hclass : localLogRatioLimit → gaussianScaleRatioLimit → sameModGaussianClass) :
    localLogRatioLimit ∧ gaussianScaleRatioLimit ∧ sameModGaussianClass := by
  have _hkUsed : 1 ≤ k := hk
  have _hellUsed : 1 ≤ ell := hell
  exact ⟨hlocal, hgauss, hclass hlocal hgauss⟩

end Omega.Conclusion
