namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-oddtail-rh-interface-genuinely-nonlocal`. -/
theorem paper_conclusion_oddtail_rh_interface_genuinely_nonlocal
    (FiniteLocalRealizable RHSensitive GenuinelyNonlocal : Prop)
    (h_blind : FiniteLocalRealizable -> ¬ RHSensitive) (h_sensitive : RHSensitive)
    (h_nonlocal : (FiniteLocalRealizable -> False) -> GenuinelyNonlocal) :
    GenuinelyNonlocal := by
  exact h_nonlocal (fun hFiniteLocal => h_blind hFiniteLocal h_sensitive)

end Omega.Conclusion
