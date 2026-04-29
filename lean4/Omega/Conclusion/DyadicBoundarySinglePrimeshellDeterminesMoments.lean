import Omega.Conclusion.BoundarySingleIntegerArithmeticMomentCompleteness

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-dyadic-boundary-single-primeshell-determines-moments`.
The SPG boundary Gödel readout gives every monomial moment, while the conclusion-level boundary
single-integer package provides injectivity of the boundary Gödel code. -/
theorem paper_conclusion_dyadic_boundary_single_primeshell_determines_moments :
    (∀ (α : Omega.SPG.MultiIndex) (U : Omega.SPG.DyadicPolycube),
      Omega.SPG.monomialMoment α U =
        Omega.SPG.boundaryMomentFromGodel α (Omega.SPG.boundaryGodelCode U)) ∧
      Function.Injective (Omega.SPG.boundaryGodelCode :
        Omega.SPG.DyadicPolycube → Omega.SPG.BoundaryGodelCode) := by
  refine ⟨Omega.SPG.paper_spg_boundary_godel_moment_readout, ?_⟩
  exact (paper_conclusion_boundary_single_integer_arithmetic_moment_completeness 0 0).2.2

end Omega.Conclusion
