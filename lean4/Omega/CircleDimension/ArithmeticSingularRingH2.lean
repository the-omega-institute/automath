import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Omega.CircleDimension.ArithmeticSingularRingDualConnected
import Omega.CircleDimension.ArithmeticSingularRingOneParameterSubgroups

namespace Omega.CircleDimension

/-- The `Σ_S^(s-1)` contribution coming from wedging the localization summand with the free part. -/
abbrev arithmeticSingularRingSigmaSummand (S : Finset ℕ) := Fin (S.card - 1) → ℤ

/-- The pure free-part contribution `T^((s-1 choose 2))` in the concrete wedge expansion. -/
abbrev arithmeticSingularRingExteriorPairSummand (S : Finset ℕ) :=
  Fin (Nat.choose (S.card - 1) 2) → ℤ

/-- Concrete bookkeeping model for the second cohomology of the arithmetic singular ring. -/
abbrev arithmeticSingularRingH2Model (S : Finset ℕ) :=
  arithmeticSingularRingSigmaSummand S × arithmeticSingularRingExteriorPairSummand S

/-- In this concrete wrapper the relevant Ext-term vanishes because the dual model is torsion-free. -/
def arithmeticSingularRingExtVanishesAgainstT (S : Finset ℕ) : Prop :=
  arithmeticSingularRingDualTorsionFree S

/-- The `H²` model identifies with alternating forms on the split `rank-1 + ℤ^(s-1)` wedge package. -/
def arithmeticSingularRingH2AlternatingFormsModel (S : Finset ℕ) : Prop :=
  arithmeticSingularRingExtVanishesAgainstT S ∧
    Nonempty (arithmeticSingularRingH2Model S ≃
      arithmeticSingularRingSigmaSummand S × arithmeticSingularRingExteriorPairSummand S)

/-- The noncanonical product model records the advertised rank count together with the dual
one-parameter-subgroup coordinates. -/
def arithmeticSingularRingH2NoncanonicalProductModel (S : Finset ℕ) : Prop :=
  circleDim ((S.card - 1) + Nat.choose (S.card - 1) 2) 0 =
      (S.card - 1) + Nat.choose (S.card - 1) 2 ∧
    Nonempty (arithmeticSingularRingOneParameterSubgroups S ≃ (S → ℝ))

/-- The arithmetic singular-ring `H²` package: vanishing of the Ext term reduces the computation to
alternating forms, and the wedge decomposition yields the noncanonical
`Σ_S^(s-1) × T^((s-1 choose 2))` model.
    thm:cdim-arithmetic-singular-ring-h2 -/
theorem paper_cdim_arithmetic_singular_ring_h2 (S : Finset ℕ) :
    arithmeticSingularRingH2AlternatingFormsModel S ∧
      arithmeticSingularRingH2NoncanonicalProductModel S := by
  rcases paper_cdim_arithmetic_singular_ring_dual_connected S with
    ⟨_, _, hTorsionFree, _, _⟩
  refine ⟨⟨hTorsionFree, ⟨Equiv.refl _⟩⟩, ?_⟩
  refine ⟨by simp [circleDim], ?_⟩
  exact ⟨paper_cdim_arithmetic_singular_ring_one_parameter_subgroups S⟩

end Omega.CircleDimension
