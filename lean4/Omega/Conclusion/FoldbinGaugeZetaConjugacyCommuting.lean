import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-foldbin-gauge-zeta-conjugacy-commuting`. -/
theorem paper_conclusion_foldbin_gauge_zeta_conjugacy_commuting
    (directProductDecomposition representationZetaFactorization conjugacyClassCount
      commutingProbabilityFormula m6Specialization : Prop)
    (hprod : directProductDecomposition)
    (hzeta : directProductDecomposition -> representationZetaFactorization)
    (hclass : directProductDecomposition -> conjugacyClassCount)
    (hcp : conjugacyClassCount -> commutingProbabilityFormula)
    (hm6 :
      representationZetaFactorization -> conjugacyClassCount -> commutingProbabilityFormula ->
        m6Specialization) :
    representationZetaFactorization ∧ conjugacyClassCount ∧ commutingProbabilityFormula ∧
      m6Specialization := by
  have hz : representationZetaFactorization := hzeta hprod
  have hc : conjugacyClassCount := hclass hprod
  have hp : commutingProbabilityFormula := hcp hc
  exact ⟨hz, hc, hp, hm6 hz hc hp⟩

end Omega.Conclusion
