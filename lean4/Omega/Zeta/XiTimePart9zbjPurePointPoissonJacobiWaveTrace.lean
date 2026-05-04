namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part9zbj-pure-point-poisson-jacobi-wave-trace`. -/
theorem paper_xi_time_part9zbj_pure_point_poisson_jacobi_wave_trace
    (integerComb phiComb noContinuousBackground : Prop)
    (hInt : integerComb)
    (hPhi : phiComb)
    (hNoBg : integerComb -> phiComb -> noContinuousBackground) :
    integerComb ∧ phiComb ∧ noContinuousBackground := by
  exact ⟨hInt, hPhi, hNoBg hInt hPhi⟩

end Omega.Zeta
