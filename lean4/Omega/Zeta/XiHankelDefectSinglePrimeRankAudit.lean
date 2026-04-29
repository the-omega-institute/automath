import Mathlib

/-- Paper label: `prop:xi-hankel-defect-single-prime-rank-audit`. -/
theorem paper_xi_hankel_defect_single_prime_rank_audit
    (rankWitness goodPrimeRank goodPrimeKernel badPrimeFinite samplingFailureVanishes : Prop)
    (hRank : rankWitness -> goodPrimeRank ∧ goodPrimeKernel)
    (hBad : rankWitness -> badPrimeFinite)
    (hSampling : badPrimeFinite -> samplingFailureVanishes) :
    rankWitness -> goodPrimeRank ∧ goodPrimeKernel ∧ badPrimeFinite ∧
      samplingFailureVanishes := by
  intro hWitness
  exact ⟨(hRank hWitness).1, (hRank hWitness).2, hBad hWitness,
    hSampling (hBad hWitness)⟩
