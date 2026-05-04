namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zbh-foldpi-positive-trace-class-rh`. -/
theorem paper_xi_time_part9zbh_foldpi_positive_trace_class_rh
    (RH determinantRepresentation spectrumIdentification unitaryUniqueness : Prop)
    (hForward : RH -> determinantRepresentation ∧ spectrumIdentification ∧ unitaryUniqueness)
    (hReverse : determinantRepresentation -> RH) :
    (RH ↔ determinantRepresentation) ∧ (RH -> spectrumIdentification ∧ unitaryUniqueness) := by
  refine ⟨?_, ?_⟩
  · exact ⟨fun hRH => (hForward hRH).1, hReverse⟩
  · intro hRH
    exact (hForward hRH).2

end Omega.Zeta
