import Omega.CircleDimension.ImplementationStructuralHalfCircleDimension
import Omega.Conclusion.CdimRankShortExactAdditivity

namespace Omega.Conclusion

open Omega.CircleDimension

/-- Paper-facing conclusion package: the canonical implementation embedding is injective, but the
structural circle dimension of a nontrivial short exact extension remains additive and therefore
does not collapse to the one-dimensional implementation scale. -/
def paper_conclusion_implementation_injection_never_structural_dim_drop_stmt : Prop :=
  Function.Injective
      killo_implementation_vs_structural_half_circle_dimension_impl_embedding ∧
    killo_implementation_vs_structural_half_circle_dimension_impl_dim = (1 : ℚ) / 2 ∧
    circleDim 2 0 = circleDim 1 0 + circleDim 1 0 ∧
    circleDim 2 0 ≠ circleDim 1 0

theorem paper_conclusion_implementation_injection_never_structural_dim_drop :
    paper_conclusion_implementation_injection_never_structural_dim_drop_stmt := by
  rcases paper_killo_implementation_vs_structural_half_circle_dimension with
    ⟨_, _, hInj, hImplDim⟩
  have hShort :
      circleDim 2 0 = circleDim 1 0 + circleDim 1 0 :=
    (paper_conclusion_cdim_rank_and_short_exact_additivity 1 2 1 0 0 0 rfl).2
  refine ⟨hInj, hImplDim, hShort, ?_⟩
  simp [circleDim]

end Omega.Conclusion
