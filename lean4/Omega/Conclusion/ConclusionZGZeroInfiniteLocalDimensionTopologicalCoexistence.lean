import Omega.Conclusion.ConclusionZgFullLocalDimensionSpectrumEveryCylinder

namespace Omega.Conclusion

open conclusion_zg_full_local_dimension_spectrum_every_cylinder_data

/-- Concrete data for the ZG zero/infinite topological coexistence corollary, built from the
already verified cylinder-local full-spectrum model. -/
structure conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data where
  fullSpectrumData : conclusion_zg_full_local_dimension_spectrum_every_cylinder_data := {}

namespace conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data

/-- Address cylinders inherited from the full local-dimension spectrum theorem. -/
abbrev cylinder
    (D : conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data) : Type :=
  D.fullSpectrumData.conclusion_zg_full_local_dimension_spectrum_every_cylinder_cylinder

/-- Witness points inherited from the full local-dimension spectrum theorem. -/
abbrev point
    (D : conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data) : Type :=
  D.fullSpectrumData.conclusion_zg_full_local_dimension_spectrum_every_cylinder_point

/-- Nonempty-cylinder predicate inherited from the full local-dimension spectrum theorem. -/
def cylinderNonempty
    (D : conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data)
    (C : D.cylinder) : Prop :=
  D.fullSpectrumData.conclusion_zg_full_local_dimension_spectrum_every_cylinder_nonempty C

/-- Membership in the image of a cylinder. -/
def inCylinder
    (D : conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data)
    (x : D.point) (C : D.cylinder) : Prop :=
  D.fullSpectrumData.conclusion_zg_full_local_dimension_spectrum_every_cylinder_mem_image x C

/-- Zero local dimension in the inherited concrete spectrum model. -/
def isZeroDimensional
    (D : conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data)
    (x : D.point) : Prop :=
  D.fullSpectrumData.conclusion_zg_full_local_dimension_spectrum_every_cylinder_local_dimension x
    .conclusion_zg_full_local_dimension_spectrum_every_cylinder_zero

/-- Infinite local dimension in the inherited concrete spectrum model. -/
def isInfiniteDimensional
    (D : conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data)
    (x : D.point) : Prop :=
  D.fullSpectrumData.conclusion_zg_full_local_dimension_spectrum_every_cylinder_local_dimension x
    .conclusion_zg_full_local_dimension_spectrum_every_cylinder_infinity

/-- Density of the zero-dimensional layer, expressed by hitting every nonempty cylinder. -/
def zeroLayerDense
    (D : conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data) : Prop :=
  ∀ C : D.cylinder, D.cylinderNonempty C →
    ∃ x : D.point, D.inCylinder x C ∧ D.isZeroDimensional x

/-- Dense `G_delta` certificate for the infinite layer, represented as a countable family of
dense cylinder predicates together with the resulting dense infinite-dimensional layer. -/
def infiniteLayerDenseGdelta
    (D : conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data) : Prop :=
  (∀ _M _R : ℕ, ∀ C : D.cylinder, D.cylinderNonempty C →
    ∃ x : D.point, D.inCylinder x C ∧ D.isInfiniteDimensional x) ∧
      ∀ C : D.cylinder, D.cylinderNonempty C →
        ∃ x : D.point, D.inCylinder x C ∧ D.isInfiniteDimensional x

end conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data

/-- Paper label: `cor:conclusion-zg-zero-infinite-local-dimension-topological-coexistence`. -/
theorem paper_conclusion_zg_zero_infinite_local_dimension_topological_coexistence
    (D : conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data) :
    D.zeroLayerDense ∧ D.infiniteLayerDenseGdelta := by
  constructor
  · intro C hC
    have hzero :=
      paper_conclusion_zg_full_local_dimension_spectrum_every_cylinder D.fullSpectrumData C
        (.conclusion_zg_full_local_dimension_spectrum_every_cylinder_zero) hC
    simpa [
      conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data.inCylinder,
      conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data.isZeroDimensional]
      using hzero
  · constructor
    · intro _M _R C hC
      have hinf :=
        paper_conclusion_zg_full_local_dimension_spectrum_every_cylinder D.fullSpectrumData C
          (.conclusion_zg_full_local_dimension_spectrum_every_cylinder_infinity) hC
      simpa [
        conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data.inCylinder,
        conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data.isInfiniteDimensional]
        using hinf
    · intro C hC
      have hinf :=
        paper_conclusion_zg_full_local_dimension_spectrum_every_cylinder D.fullSpectrumData C
          (.conclusion_zg_full_local_dimension_spectrum_every_cylinder_infinity) hC
      simpa [
        conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data.inCylinder,
        conclusion_zg_zero_infinite_local_dimension_topological_coexistence_data.isInfiniteDimensional]
        using hinf

end Omega.Conclusion
