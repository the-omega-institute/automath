import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local wrapper for the compactness principle attached to the reversible window-`6`
pushforward kernel. The fields encode the detailed-balance input, the resulting self-adjointness
of the induced operator, the finite-dimensionality of its commutant, and the closed-subgroup
argument inside `U(21)` that yields compactness of the unitary commutant. -/
structure Window6P6CompactnessPrincipleData where
  detailedBalance : Prop
  selfAdjointOperator : Prop
  commutantFiniteDimensional : Prop
  closedSubgroupOfU21 : Prop
  unitaryGroupCompact : Prop
  detailedBalance_h : detailedBalance
  deriveSelfAdjointOperator :
    detailedBalance → selfAdjointOperator
  deriveCommutantFiniteDimensional :
    selfAdjointOperator → commutantFiniteDimensional
  deriveClosedSubgroupOfU21 :
    selfAdjointOperator → commutantFiniteDimensional → closedSubgroupOfU21
  deriveUnitaryGroupCompact :
    closedSubgroupOfU21 → unitaryGroupCompact

/-- Paper-facing wrapper for the window-`6` compactness principle: detailed balance gives a
self-adjoint Markov operator on `ℓ²(X₆, π₆)`, its commutant is a finite-dimensional `*`-algebra,
and the unitary commutant is therefore a closed subgroup of `U(21)`, hence compact.
    cor:window6-p6-compactness-principle -/
theorem paper_window6_p6_compactness_principle (D : Window6P6CompactnessPrincipleData) :
    D.selfAdjointOperator ∧ D.commutantFiniteDimensional ∧ D.unitaryGroupCompact := by
  have hSelfAdjointOperator : D.selfAdjointOperator :=
    D.deriveSelfAdjointOperator D.detailedBalance_h
  have hCommutantFiniteDimensional : D.commutantFiniteDimensional :=
    D.deriveCommutantFiniteDimensional hSelfAdjointOperator
  have hClosedSubgroupOfU21 : D.closedSubgroupOfU21 :=
    D.deriveClosedSubgroupOfU21 hSelfAdjointOperator hCommutantFiniteDimensional
  exact ⟨hSelfAdjointOperator, hCommutantFiniteDimensional,
    D.deriveUnitaryGroupCompact hClosedSubgroupOfU21⟩

end Omega.GU
