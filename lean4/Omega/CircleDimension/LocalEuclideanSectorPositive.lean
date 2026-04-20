import Mathlib

namespace Omega.CircleDimension

/-- The ambient three-dimensional audited local sector. -/
abbrev LocalSectorVec := EuclideanSpace ℝ (Fin 3)

/-- The local Euclidean sector is modeled by a real linear map `A`, with quadratic form
`h_* = Aᵀ A`, encoded as `v ↦ ‖A v‖²`. Injectivity of `A` is the nondegeneracy hypothesis. -/
structure LocalEuclideanSectorData where
  matrix : LocalSectorVec →ₗ[ℝ] LocalSectorVec
  matrix_nondegenerate : Function.Injective matrix

/-- The quadratic form attached to the audited local Euclidean sector. -/
noncomputable def LocalEuclideanSectorData.quad (D : LocalEuclideanSectorData)
    (v : LocalSectorVec) : ℝ :=
  ‖D.matrix v‖ ^ 2

/-- The audited local Euclidean sector is positive on every nonzero vector. -/
theorem paper_cdim_local_euclidean_sector_positive (D : LocalEuclideanSectorData) :
    ∀ v, v ≠ 0 → 0 < D.quad v := by
  intro v hv
  have hmatrix : D.matrix v ≠ 0 := by
    intro hzero
    apply hv
    exact D.matrix_nondegenerate (by simpa using hzero)
  have hnorm : ‖D.matrix v‖ ≠ 0 := by
    simpa using norm_ne_zero_iff.mpr hmatrix
  simpa [LocalEuclideanSectorData.quad] using sq_pos_of_ne_zero hnorm

/-- Euclidean-sector corollary: the quadratic form vanishes only at the zero vector. -/
lemma localEuclideanSector_quad_eq_zero_iff (D : LocalEuclideanSectorData) (v : LocalSectorVec) :
    D.quad v = 0 ↔ v = 0 := by
  constructor
  · intro hquad
    by_contra hv
    have hpos := paper_cdim_local_euclidean_sector_positive D v hv
    linarith
  · intro hv
    simp [LocalEuclideanSectorData.quad, hv]

end Omega.CircleDimension
