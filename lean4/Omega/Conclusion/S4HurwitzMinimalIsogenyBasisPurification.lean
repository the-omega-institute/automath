import Omega.Folding.KilloS4Genus49JacobianComputableIsogeny
import Omega.Zeta.XiTimePart9n1bPrymChevalleyWeilReciprocity

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-s4-hurwitz-minimal-isogeny-basis-purification`. -/
theorem paper_conclusion_s4_hurwitz_minimal_isogeny_basis_purification (Q : Polynomial ℚ)
    (D : Omega.Zeta.xi_time_part9n1b_prym_chevalley_weil_reciprocity_data) :
    Omega.Folding.killo_s4_genus49_jacobian_computable_isogeny_factor_dimensions =
      [5, 4, 3, 9] ∧
    Omega.Folding.killo_s4_genus49_jacobian_computable_isogeny_factor_multiplicities =
      [1, 2, 3, 3] ∧
    Omega.Zeta.xi_time_part9n1b_prym_chevalley_weil_reciprocity_statement D := by
  rcases Omega.Folding.paper_killo_s4_genus49_jacobian_computable_isogeny Q with
    ⟨_, _, _, hDimensions, hMultiplicities, _⟩
  exact ⟨hDimensions, hMultiplicities,
    Omega.Zeta.paper_xi_time_part9n1b_prym_chevalley_weil_reciprocity D⟩

end Omega.Conclusion
