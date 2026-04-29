import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

namespace Omega.Zeta

universe u

/-- Concrete finite-dimensional model for the relative-commutant index cap. The relative
commutant is represented by a finite real vector space; an orthogonal nonzero projection family is
recorded through the resulting linear independence of its elements. -/
structure dephys_relative_commutant_dimension_index_cap_data where
  RelativeCommutant : Type u
  [relativeCommutantAdd : AddCommGroup RelativeCommutant]
  [relativeCommutantModule : Module ℝ RelativeCommutant]
  [relativeCommutantFinite : Module.Finite ℝ RelativeCommutant]
  indexCap : ℕ
  projectionCount : ℕ
  projections : Fin projectionCount → RelativeCommutant
  dimensionIndexBound : Module.finrank ℝ RelativeCommutant ≤ indexCap
  projectionsLinearIndependent : LinearIndependent ℝ projections

namespace dephys_relative_commutant_dimension_index_cap_data

/-- Finite dimensionality of the concrete relative commutant. -/
def relativeCommutantFiniteDimensional
    (D : dephys_relative_commutant_dimension_index_cap_data) : Prop :=
  letI := D.relativeCommutantAdd
  letI := D.relativeCommutantModule
  Module.Finite ℝ D.RelativeCommutant

/-- Jones/Pimsner--Popa index cap encoded as a finrank bound. -/
def dimensionIndexCap (D : dephys_relative_commutant_dimension_index_cap_data) : Prop :=
  letI := D.relativeCommutantAdd
  letI := D.relativeCommutantModule
  Module.finrank ℝ D.RelativeCommutant ≤ D.indexCap

/-- Any linearly independent family of nonzero orthogonal projections has cardinality at most the
index cap. -/
def orthogonalProjectionFamilyCap
    (D : dephys_relative_commutant_dimension_index_cap_data) : Prop :=
  D.projectionCount ≤ D.indexCap

end dephys_relative_commutant_dimension_index_cap_data

open dephys_relative_commutant_dimension_index_cap_data

/-- Paper label: `prop:dephys-relative-commutant-dimension-index-cap`. Finite index is encoded by
a finite-dimensional relative-commutant model whose finrank is capped by the index; a family of
pairwise orthogonal nonzero projections is linearly independent, hence its cardinality is bounded
by the finrank and therefore by the same index cap. -/
theorem paper_dephys_relative_commutant_dimension_index_cap
    (D : dephys_relative_commutant_dimension_index_cap_data) :
    D.relativeCommutantFiniteDimensional ∧ D.dimensionIndexCap ∧
      D.orthogonalProjectionFamilyCap := by
  letI := D.relativeCommutantAdd
  letI := D.relativeCommutantModule
  letI := D.relativeCommutantFinite
  refine ⟨?_, ?_, ?_⟩
  · exact D.relativeCommutantFinite
  · exact D.dimensionIndexBound
  · have hCard : D.projectionCount ≤ Module.finrank ℝ D.RelativeCommutant := by
      have h := D.projectionsLinearIndependent.fintype_card_le_finrank
      simpa using h
    exact le_trans hCard D.dimensionIndexBound

end Omega.Zeta
