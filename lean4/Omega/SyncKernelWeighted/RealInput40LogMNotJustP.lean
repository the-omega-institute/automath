import Omega.SyncKernelWeighted.RealInput40IsobaricDriftCapacity

namespace Omega.SyncKernelWeighted

open RealInput40IsobaricDriftData

/-- Paper label: `cor:real-input-40-logM-not-just-P`. If `gradLogM` were a scalar multiple of
`gradP`, then its orthogonal projection to the isobaric slice would vanish identically, contrary
to the nonzero projected drift witness. -/
theorem paper_real_input_40_logm_not_just_p
    (D : RealInput40IsobaricDriftData) (hproj : D.isobaricProjection ≠ 0) :
    ¬ ∃ c : Real, D.gradLogM = c • D.gradP := by
  rintro ⟨c, hc⟩
  have hpp_ne : realInput40Inner D.gradP D.gradP ≠ 0 := by
    unfold realInput40Inner
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr D.gradP_ne_zero)
  have hpp_ne_inner : inner ℝ D.gradP D.gradP ≠ 0 := by
    simpa [realInput40Inner] using hpp_ne
  have hcoeff :
      realInput40Inner (c • D.gradP) D.gradP / realInput40Inner D.gradP D.gradP = c := by
    unfold realInput40Inner
    rw [real_inner_smul_left]
    field_simp [hpp_ne_inner]
  have hproj_zero : D.isobaricProjection = 0 := by
    unfold RealInput40IsobaricDriftData.isobaricProjection
    rw [hc, hcoeff, sub_self]
  exact hproj hproj_zero

end Omega.SyncKernelWeighted
