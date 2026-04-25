import Mathlib.Tactic
import Omega.CircleDimension.ArithmeticSingularRingDualConnected
import Omega.CircleDimension.ArithmeticSingularRingOneParameterSubgroups

namespace Omega.DerivedConsequences

/-- The connectedness/rank/self-parameterization package for the arithmetic singular ring over the
finite prime support `S`. -/
def derived_arithmetic_singular_ring_rank_self_parameterization_statement (S : Finset ℕ) : Prop :=
  Omega.CircleDimension.arithmeticSingularRingConnected S ∧
    Omega.CircleDimension.arithmeticSingularRingDualRank S = S.card ∧
    Nonempty (Omega.CircleDimension.ArithmeticSingularRingOneParameterSubgroup S ≃ (S → ℝ))

/-- Paper label: `thm:derived-arithmetic-singular-ring-rank-self-parameterization`. The existing
dual-connectedness wrapper gives connectedness and the expected free rank, while the verified
one-parameter-subgroup model identifies the arithmetic singular ring with its torus-frequency
vector space. -/
theorem paper_derived_arithmetic_singular_ring_rank_self_parameterization (S : Finset ℕ) :
    Omega.CircleDimension.arithmeticSingularRingConnected S ∧
      Omega.CircleDimension.arithmeticSingularRingDualRank S = S.card ∧
      Nonempty (Omega.CircleDimension.ArithmeticSingularRingOneParameterSubgroup S ≃ (S → ℝ)) := by
  rcases Omega.CircleDimension.paper_cdim_arithmetic_singular_ring_dual_connected S with
    ⟨_, _, _, hconnected, hrank⟩
  refine ⟨hconnected, ?_, ?_⟩
  · simpa [Omega.CircleDimension.circleDim] using hrank
  · exact ⟨Omega.CircleDimension.paper_cdim_arithmetic_singular_ring_one_parameter_subgroups S⟩

end Omega.DerivedConsequences
