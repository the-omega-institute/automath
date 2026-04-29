namespace Omega.Zeta

/-- prop:xi-cauchy-poisson-tv-kl-sharp-interface -/
theorem paper_xi_cauchy_poisson_tv_kl_sharp_interface
    (tvMain klMain sixthOrder pinskerRatio : Prop)
    (hTV : tvMain)
    (hKL : klMain)
    (hSixth : sixthOrder)
    (hPinsker : pinskerRatio) :
    tvMain ∧ klMain ∧ sixthOrder ∧ pinskerRatio := by
  exact ⟨hTV, hKL, hSixth, hPinsker⟩

end Omega.Zeta
