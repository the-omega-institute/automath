import Omega.POM.EulerDefectOrthogonalPythagoras

namespace Omega.POM

theorem paper_pom_euler_defect_min_action_gauge
    (f : pom_euler_defect_orthogonal_pythagoras_fn) :
    pom_euler_defect_orthogonal_pythagoras_norm_sq
        (pom_euler_defect_orthogonal_pythagoras_interaction_component f) =
      pom_euler_defect_orthogonal_pythagoras_norm_sq f -
        (pom_euler_defect_orthogonal_pythagoras_norm_sq
            (pom_euler_defect_orthogonal_pythagoras_const_component f) +
          pom_euler_defect_orthogonal_pythagoras_norm_sq
            (pom_euler_defect_orthogonal_pythagoras_axis1_component f) +
          pom_euler_defect_orthogonal_pythagoras_norm_sq
            (pom_euler_defect_orthogonal_pythagoras_axis2_component f)) := by
  let D : pom_euler_defect_orthogonal_pythagoras_data := {}
  have h :=
    paper_pom_euler_defect_orthogonal_pythagoras D f
  rcases h with ⟨_, _, _, _, _, _, _, hnorm⟩
  linarith

end Omega.POM
