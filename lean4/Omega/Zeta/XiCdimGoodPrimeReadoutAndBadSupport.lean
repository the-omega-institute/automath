namespace Omega.Zeta

/-- Paper label: `prop:xi-cdim-good-prime-readout-and-bad-support`. -/
theorem paper_xi_cdim_good_prime_readout_and_bad_support
    (goodPrimeReadout badPrimeSupportReadout : Prop)
    (hgood : goodPrimeReadout) (hbad : badPrimeSupportReadout) :
    And goodPrimeReadout badPrimeSupportReadout := by
  exact And.intro hgood hbad

end Omega.Zeta
