namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-realinput40-zero-temp-two-compression-failures`. The two
zero-temperature obstructions are applied independently and then paired. -/
theorem paper_conclusion_realinput40_zero_temp_two_compression_failures
    (noncrystallization irreversible_infinite_entropy no_finite_periodic_compression
      no_reversible_parry_compression : Prop)
    (h_noncryst : noncrystallization -> no_finite_periodic_compression)
    (h_irrev : irreversible_infinite_entropy -> no_reversible_parry_compression)
    (h1 : noncrystallization)
    (h2 : irreversible_infinite_entropy) :
    no_finite_periodic_compression ∧ no_reversible_parry_compression := by
  exact ⟨h_noncryst h1, h_irrev h2⟩

end Omega.Conclusion
