import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete certificate data for a nonabelian Stokes--Bianchi cube.  The face terms are already
transported to a common base point; the third-order Bianchi term cancels, leaving only the
fourth-order Magnus remainder. -/
structure conclusion_nonabelian_stokes_bianchi_cube_certificate_Data where
  h : ℝ
  C : ℝ
  cubeHolonomyDefect : ℝ
  transportedFaceTerm : Fin 6 → ℝ
  transportedFaceSum : ℝ
  bianchiThirdOrderTerm : ℝ
  magnusRemainder : ℝ
  transportedFaceSum_eq : transportedFaceSum = ∑ face, transportedFaceTerm face
  cube_defect_expansion :
    cubeHolonomyDefect = transportedFaceSum + bianchiThirdOrderTerm + magnusRemainder
  transported_faces_cancel : transportedFaceSum = 0
  bianchi_cancellation : bianchiThirdOrderTerm = 0
  magnus_remainder_bound : |magnusRemainder| ≤ C * h ^ 4

namespace conclusion_nonabelian_stokes_bianchi_cube_certificate_Data

/-- The Bianchi cube defect is fourth order in the edge length. -/
def bianchi_cube_defect_bound
    (D : conclusion_nonabelian_stokes_bianchi_cube_certificate_Data) : Prop :=
  |D.cubeHolonomyDefect| ≤ D.C * D.h ^ 4

end conclusion_nonabelian_stokes_bianchi_cube_certificate_Data

open conclusion_nonabelian_stokes_bianchi_cube_certificate_Data

/-- Paper label: `thm:conclusion-nonabelian-stokes-bianchi-cube-certificate`. -/
theorem paper_conclusion_nonabelian_stokes_bianchi_cube_certificate
    (D : conclusion_nonabelian_stokes_bianchi_cube_certificate_Data) :
    D.bianchi_cube_defect_bound := by
  calc
    |D.cubeHolonomyDefect| = |D.magnusRemainder| := by
      rw [D.cube_defect_expansion, D.transported_faces_cancel, D.bianchi_cancellation]
      simp
    _ ≤ D.C * D.h ^ 4 := D.magnus_remainder_bound

end Omega.Conclusion
