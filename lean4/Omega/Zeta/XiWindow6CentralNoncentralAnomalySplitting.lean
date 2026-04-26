import Mathlib.Tactic

namespace Omega.Zeta

abbrev xi_window6_central_noncentral_anomaly_splitting_central_fibers := Fin 8

abbrev xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers := Fin 13

abbrev xi_window6_central_noncentral_anomaly_splitting_all_fibers :=
  xi_window6_central_noncentral_anomaly_splitting_central_fibers ⊕
    xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers

abbrev xi_window6_central_noncentral_anomaly_splitting_boundary_center := Fin 3

abbrev xi_window6_central_noncentral_anomaly_splitting_center_boundary_quotient := Fin 5

abbrev xi_window6_central_noncentral_anomaly_splitting_boundary_quotient := Fin 18

abbrev xi_window6_central_noncentral_anomaly_splitting_sign_space (ι : Type) :=
  ι → ZMod 2

def xi_window6_central_noncentral_anomaly_splitting_project_central
    (x : xi_window6_central_noncentral_anomaly_splitting_sign_space
      xi_window6_central_noncentral_anomaly_splitting_all_fibers) :
    xi_window6_central_noncentral_anomaly_splitting_sign_space
      xi_window6_central_noncentral_anomaly_splitting_central_fibers :=
  fun i => x (Sum.inl i)

def xi_window6_central_noncentral_anomaly_splitting_project_noncentral
    (x : xi_window6_central_noncentral_anomaly_splitting_sign_space
      xi_window6_central_noncentral_anomaly_splitting_all_fibers) :
    xi_window6_central_noncentral_anomaly_splitting_sign_space
      xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers :=
  fun i => x (Sum.inr i)

def xi_window6_central_noncentral_anomaly_splitting_combine
    (p :
      xi_window6_central_noncentral_anomaly_splitting_sign_space
          xi_window6_central_noncentral_anomaly_splitting_central_fibers ×
        xi_window6_central_noncentral_anomaly_splitting_sign_space
          xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers) :
    xi_window6_central_noncentral_anomaly_splitting_sign_space
      xi_window6_central_noncentral_anomaly_splitting_all_fibers :=
  Sum.elim p.1 p.2

def xi_window6_central_noncentral_anomaly_splitting_equiv :
    xi_window6_central_noncentral_anomaly_splitting_sign_space
        xi_window6_central_noncentral_anomaly_splitting_all_fibers ≃
      xi_window6_central_noncentral_anomaly_splitting_sign_space
          xi_window6_central_noncentral_anomaly_splitting_central_fibers ×
        xi_window6_central_noncentral_anomaly_splitting_sign_space
          xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers where
  toFun x :=
    (xi_window6_central_noncentral_anomaly_splitting_project_central x,
      xi_window6_central_noncentral_anomaly_splitting_project_noncentral x)
  invFun := xi_window6_central_noncentral_anomaly_splitting_combine
  left_inv x := by
    funext i
    cases i <;> rfl
  right_inv p := by
    ext i <;> rfl

def xi_window6_central_noncentral_anomaly_splitting_statement : Prop :=
  Fintype.card xi_window6_central_noncentral_anomaly_splitting_central_fibers = 8 ∧
    Fintype.card xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers = 13 ∧
    Fintype.card xi_window6_central_noncentral_anomaly_splitting_all_fibers = 21 ∧
    Nonempty
      (xi_window6_central_noncentral_anomaly_splitting_sign_space
          xi_window6_central_noncentral_anomaly_splitting_all_fibers ≃
        xi_window6_central_noncentral_anomaly_splitting_sign_space
            xi_window6_central_noncentral_anomaly_splitting_central_fibers ×
          xi_window6_central_noncentral_anomaly_splitting_sign_space
            xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers) ∧
    Fintype.card xi_window6_central_noncentral_anomaly_splitting_boundary_center = 3 ∧
    Fintype.card xi_window6_central_noncentral_anomaly_splitting_center_boundary_quotient = 5 ∧
    Fintype.card xi_window6_central_noncentral_anomaly_splitting_boundary_quotient = 18 ∧
    Fintype.card xi_window6_central_noncentral_anomaly_splitting_central_fibers +
        Fintype.card xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers =
      Fintype.card xi_window6_central_noncentral_anomaly_splitting_all_fibers ∧
    Fintype.card xi_window6_central_noncentral_anomaly_splitting_center_boundary_quotient +
        Fintype.card xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers =
      Fintype.card xi_window6_central_noncentral_anomaly_splitting_boundary_quotient

/-- Paper label: `thm:xi-window6-central-noncentral-anomaly-splitting`. -/
theorem paper_xi_window6_central_noncentral_anomaly_splitting :
    xi_window6_central_noncentral_anomaly_splitting_statement := by
  refine ⟨?_, ?_, ?_, ⟨xi_window6_central_noncentral_anomaly_splitting_equiv⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_window6_central_noncentral_anomaly_splitting_central_fibers]
  · norm_num [xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers]
  · norm_num [xi_window6_central_noncentral_anomaly_splitting_all_fibers,
      xi_window6_central_noncentral_anomaly_splitting_central_fibers,
      xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers]
  · norm_num [xi_window6_central_noncentral_anomaly_splitting_boundary_center]
  · norm_num [xi_window6_central_noncentral_anomaly_splitting_center_boundary_quotient]
  · norm_num [xi_window6_central_noncentral_anomaly_splitting_boundary_quotient]
  · norm_num [xi_window6_central_noncentral_anomaly_splitting_all_fibers,
      xi_window6_central_noncentral_anomaly_splitting_central_fibers,
      xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers]
  · norm_num [xi_window6_central_noncentral_anomaly_splitting_center_boundary_quotient,
      xi_window6_central_noncentral_anomaly_splitting_noncentral_fibers,
      xi_window6_central_noncentral_anomaly_splitting_boundary_quotient]

end Omega.Zeta
