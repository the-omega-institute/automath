namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zero-density-pearson-explosion-strict-separation`. -/
theorem paper_conclusion_zero_density_pearson_explosion_strict_separation
    (zeroDensitySparse pearsonIdentity pearsonDiverges : Prop)
    (hzero : zeroDensitySparse) (hpearson : pearsonIdentity) (hdiv : pearsonDiverges) :
    zeroDensitySparse ∧ pearsonIdentity ∧ pearsonDiverges := by
  exact ⟨hzero, hpearson, hdiv⟩

end Omega.Conclusion
