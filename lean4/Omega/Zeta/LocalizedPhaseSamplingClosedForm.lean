import Omega.Zeta.CdimLocalizationZetaAS

namespace Omega.Zeta

/-- Paper label: `thm:xi-localized-phase-sampling-closed-form`.
The localized phase-sampling coefficient removes exactly the prime-power factors supported on
`S`, and its values at primes recover membership in `S`. -/
theorem paper_xi_localized_phase_sampling_closed_form (S : Finset ℕ) :
    (∀ N : ℕ, xiLocalizedCoeff S N =
      N.factorization.prod (fun p k => if p ∈ S then 1 else p ^ k)) ∧
    (∀ p : ℕ, Nat.Prime p →
      ((xiLocalizedCoeff S p = 1 ↔ p ∈ S) ∧
        (xiLocalizedCoeff S p = p ↔ p ∉ S))) := by
  refine ⟨fun N => rfl, ?_⟩
  intro p hp
  have hcoeff : xiLocalizedCoeff S p = if p ∈ S then 1 else p := by
    simpa using (xiLocalizedCoeff_prime_pow S (p := p) (k := 1) hp)
  constructor
  · constructor
    · intro h
      by_cases hpS : p ∈ S
      · exact hpS
      · have hp_coeff : xiLocalizedCoeff S p = p := by
          simpa [hpS] using hcoeff
        have hp_one : p = 1 := hp_coeff.symm.trans h
        exact False.elim (Nat.Prime.ne_one hp hp_one)
    · intro hpS
      simpa [hpS] using hcoeff
  · constructor
    · intro h
      by_cases hpS : p ∈ S
      · have hone : xiLocalizedCoeff S p = 1 := by
          simpa [hpS] using hcoeff
        have hp_one : p = 1 := h.symm.trans hone
        exact False.elim (Nat.Prime.ne_one hp hp_one)
      · exact hpS
    · intro hpS
      simpa [hpS] using hcoeff

end Omega.Zeta
