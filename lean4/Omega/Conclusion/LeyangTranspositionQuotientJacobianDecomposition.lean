import Omega.Conclusion.LeyangOffdiagonalTranspositionQuotient
import Omega.Folding.FoldGaugeAnomalyQuotientJacobiansIsotypic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-leyang-transposition-quotient-jacobian-decomposition`.
The off-diagonal self-fiber quotient is exactly the complementary transposition quotient, and the
already formalized quotient/Jacobian package identifies the resulting quotient with the Lee--Yang
curve together with the full Jacobian/Prym decomposition data. -/
theorem paper_conclusion_leyang_transposition_quotient_jacobian_decomposition
    (P : Polynomial ℚ) :
    (∀ σ : Equiv.Perm (Fin 4),
      offDiagonalPairStabilizer σ ↔ offDiagonalTranspositionQuotient σ) ∧
    (1 : Equiv.Perm (Fin 4)) ≠ offDiagonalTransposition ∧
    Nonempty
      (Omega.CircleDimension.cdim_s4_a4_quotient_is_leyang_curve_a4_quotient_point P ≃
        Omega.CircleDimension.cdim_s4_a4_quotient_is_leyang_curve_leyang_point P) ∧
    Omega.CircleDimension.s4v4CompatibleBiellipticPencils.card = 3 ∧
    (let D :=
        Omega.CircleDimension.cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting_prym_data;
      D.standardGeneratorExists ∧ D.invariantPolarizationsAreA2 ∧
        D.naturalPrymPolarizationIsA2) ∧
    Omega.CircleDimension.a2CartanForm.det = 3 := by
  rcases paper_conclusion_leyang_offdiagonal_transposition_quotient with ⟨hquot, hneq⟩
  rcases Omega.Folding.paper_fold_gauge_anomaly_quotient_jacobians_isotypic P with
    ⟨hleyang, hpencils, hprym, hdet⟩
  exact ⟨hquot, hneq, hleyang, hpencils, hprym, hdet⟩

end Omega.Conclusion
