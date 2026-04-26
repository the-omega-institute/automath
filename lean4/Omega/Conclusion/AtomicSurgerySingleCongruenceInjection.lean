import Omega.Conclusion.AtomicSurgeryFiniteCongruenceTomography

namespace Omega.Conclusion

theorem paper_conclusion_atomic_surgery_single_congruence_injection
    (D : Omega.Conclusion.paper_conclusion_atomic_surgery_finite_congruence_tomography_Data)
    (q : Nat) (hq : 0 < q) (u : Real) (hu : 0 < u) :
    (∃! a : Nat,
        a < q ∧
          Omega.Conclusion.conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D q
            a u ≠ 0) ∧
      Omega.Conclusion.conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D q
          (D.ell % q) u =
        D.m * u ^ D.E := by
  exact
    ⟨conclusion_atomic_surgery_finite_congruence_tomography_uniqueResidue D hq hu,
      conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff_eq D u⟩

end Omega.Conclusion
