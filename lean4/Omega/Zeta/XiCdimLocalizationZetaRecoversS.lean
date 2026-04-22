import Mathlib.Tactic
import Omega.Zeta.CdimLocalizationZetaAS

namespace Omega.Zeta

private lemma xi_cdim_localization_zeta_recovers_s_prime_pow_coeff
    (S : Finset ℕ) :
    ∀ {p k : ℕ}, Nat.Prime p → xiLocalizedCoeff S (p ^ k) = if p ∈ S then 1 else p ^ k := by
  have hAS :=
    paper_xi_cdim_localization_zeta_as S (∅ : Finset ℕ) (0 : ℚ) (by norm_num)
      (by
        intro p hp
        cases hp)
  intro p k hp
  exact hAS.2.1 hp

/-- Paper label: `cor:xi-cdim-localization-zeta-recovers-S`.
For finite prime supports, the localized Dirichlet coefficients on the primes are `1` on `S` and
`p` off `S`; hence equality of the prime-local data recovers the support uniquely. -/
theorem paper_xi_cdim_localization_zeta_recovers_s
    (S T : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p) :
    (∀ p : ℕ, Nat.Prime p → xiLocalizedCoeff S p = xiLocalizedCoeff T p) ↔ S = T := by
  constructor
  · intro hcoeff
    apply Finset.ext
    intro p
    by_cases hp : Nat.Prime p
    · constructor
      · intro hpS
        by_cases hpT : p ∈ T
        · exact hpT
        · have hSp : xiLocalizedCoeff S p = 1 := by
            simpa [hpS] using
              (xi_cdim_localization_zeta_recovers_s_prime_pow_coeff S (p := p) (k := 1) hp)
          have hTp : xiLocalizedCoeff T p = p := by
            simpa [hpT] using
              (xi_cdim_localization_zeta_recovers_s_prime_pow_coeff T (p := p) (k := 1) hp)
          have hEq : 1 = p := by simpa [hSp, hTp] using hcoeff p hp
          exact (Nat.Prime.ne_one hp hEq.symm).elim
      · intro hpT
        by_cases hpS : p ∈ S
        · exact hpS
        · have hSp : xiLocalizedCoeff S p = p := by
            simpa [hpS] using
              (xi_cdim_localization_zeta_recovers_s_prime_pow_coeff S (p := p) (k := 1) hp)
          have hTp : xiLocalizedCoeff T p = 1 := by
            simpa [hpT] using
              (xi_cdim_localization_zeta_recovers_s_prime_pow_coeff T (p := p) (k := 1) hp)
          have hEq : p = 1 := by simpa [hSp, hTp] using hcoeff p hp
          exact (Nat.Prime.ne_one hp hEq).elim
    · constructor
      · intro hpS
        exact False.elim (hp (hS p hpS))
      · intro hpT
        exact False.elim (hp (hT p hpT))
  · intro hST
    subst hST
    intro p hp
    rfl

end Omega.Zeta
