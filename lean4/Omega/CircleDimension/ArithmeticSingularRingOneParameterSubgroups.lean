import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- A compatible one-parameter subgroup of the arithmetic singular ring supported on `S`.
    In this concrete model the subgroup is determined by the torus-frequency assigned to each
    coordinate in `S`. -/
structure ArithmeticSingularRingOneParameterSubgroup (S : Finset ℕ) where
  torusFrequency : S → ℝ

/-- The type of compatible one-parameter subgroups supported on `S`. -/
abbrev arithmeticSingularRingOneParameterSubgroups (S : Finset ℕ) :=
  ArithmeticSingularRingOneParameterSubgroup S

/-- Extract the torus-frequency vector by coordinate projection. -/
def torusFrequencyVector {S : Finset ℕ} :
    arithmeticSingularRingOneParameterSubgroups S → (S → ℝ)
  | G => G.torusFrequency

/-- Reconstruct the compatible subgroup from its frequency vector. -/
def subgroupOfTorusFrequencyVector {S : Finset ℕ} (ω : S → ℝ) :
    arithmeticSingularRingOneParameterSubgroups S :=
  ⟨ω⟩

@[simp] theorem torusFrequencyVector_subgroupOfTorusFrequencyVector {S : Finset ℕ} (ω : S → ℝ) :
    torusFrequencyVector (subgroupOfTorusFrequencyVector ω) = ω :=
  rfl

@[simp] theorem subgroupOfTorusFrequencyVector_torusFrequencyVector {S : Finset ℕ}
    (G : arithmeticSingularRingOneParameterSubgroups S) :
    subgroupOfTorusFrequencyVector (torusFrequencyVector G) = G := by
  cases G
  rfl

/-- Compatible one-parameter subgroups of the arithmetic singular ring are equivalent to their
    torus-frequency vectors.
    thm:cdim-arithmetic-singular-ring-one-parameter-subgroups -/
noncomputable def paper_cdim_arithmetic_singular_ring_one_parameter_subgroups (S : Finset ℕ) :
    arithmeticSingularRingOneParameterSubgroups S ≃ (S → ℝ) := by
  refine
    { toFun := torusFrequencyVector
      invFun := subgroupOfTorusFrequencyVector
      left_inv := subgroupOfTorusFrequencyVector_torusFrequencyVector
      right_inv := torusFrequencyVector_subgroupOfTorusFrequencyVector }

end Omega.CircleDimension
