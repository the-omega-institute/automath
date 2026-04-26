import Omega.Zeta.XiHankelNormalformCRTAdelicMultiplicity

namespace Omega.Zeta

open XiHankelNormalformCRTData

/-- The finite support on which adelic ambiguity can survive. -/
def xi_hankel_normalform_adelic_ambiguity_finite_support_bad_primes
    (D : XiHankelNormalformCRTData) : Finset ℕ :=
  D.localModuli.filter fun q => ¬ Nat.Coprime q D.determinant

/-- Paper label: `cor:xi-hankel-normalform-adelic-ambiguity-finite-support`. Every local factor
coprime to the determinant has vanishing multiplicity and a unique local solution, so all
adelic ambiguity is supported on the finite set of determinant-dividing local factors. -/
theorem paper_xi_hankel_normalform_adelic_ambiguity_finite_support
    (D : XiHankelNormalformCRTData) :
    ∃ S : Finset ℕ,
      ∀ q ∈ D.localModuli, q ∉ S → D.localMultiplicity q = 0 ∧ D.localSolutionCount q = 1 := by
  refine ⟨xi_hankel_normalform_adelic_ambiguity_finite_support_bad_primes D, ?_⟩
  intro q hq hqS
  have hcop : Nat.Coprime q D.determinant := by
    by_contra hnot
    exact hqS <| by
      simp [xi_hankel_normalform_adelic_ambiguity_finite_support_bad_primes, hq, hnot]
  refine ⟨D.multiplicity_zero_of_coprime q hq hcop, D.localSolutionCount_eq_one_of_coprime hq hcop⟩

end Omega.Zeta
