namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-binfold-no-nontrivial-nuisance-deformation-fixed-powerdiv`. -/
theorem paper_conclusion_binfold_no_nontrivial_nuisance_deformation_fixed_powerdiv
    (fixedPowerDivergence sameGoldenParameter allLimitInvariantsFixed asymptoticallyTrivial : Prop)
    (hfixed : fixedPowerDivergence)
    (hrecover : fixedPowerDivergence → sameGoldenParameter)
    (hinvariants : sameGoldenParameter → allLimitInvariantsFixed)
    (htrivial : allLimitInvariantsFixed → asymptoticallyTrivial) :
    asymptoticallyTrivial := by
  exact htrivial (hinvariants (hrecover hfixed))

end Omega.Conclusion
