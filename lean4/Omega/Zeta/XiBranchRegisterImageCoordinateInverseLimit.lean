import Omega.Zeta.XiPrimeRegisterHistoryInverseLimit

namespace Omega.Zeta

/-- The branch-register image coordinate model used in this wrapper. -/
abbrev xi_branch_register_image_coordinate_inverse_limit_stream :=
  XiPrimeRegisterStream Unit

/-- The coherent finite-coordinate cone of branch-register prefix images. -/
abbrev xi_branch_register_image_coordinate_inverse_limit_cone :=
  XiPrimeRegisterCompatibleFamily Unit

/-- The canonical map from an infinite branch-register image to its coherent prefix cone. -/
def xi_branch_register_image_coordinate_inverse_limit_theta :
    xi_branch_register_image_coordinate_inverse_limit_stream →
      xi_branch_register_image_coordinate_inverse_limit_cone :=
  xiPrimeRegisterOfStream

/-- The branch-register image right-shift, dropping the first branch coordinate. -/
def xi_branch_register_image_coordinate_inverse_limit_stream_right_shift
    (s : xi_branch_register_image_coordinate_inverse_limit_stream) :
    xi_branch_register_image_coordinate_inverse_limit_stream :=
  (s.1, fun n => s.2 (n + 1))

/-- The finite prefix right-shift, dropping the first branch coordinate at depth `n + 1`. -/
def xi_branch_register_image_coordinate_inverse_limit_prefix_right_shift (n : ℕ) :
    XiPrimeRegisterLayer Unit (n + 1) → XiPrimeRegisterLayer Unit n
  | (x, a) => (x, fun i => a ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

/-- Concrete inverse-limit package for the branch-register image coordinates. -/
def xi_branch_register_image_coordinate_inverse_limit_statement : Prop :=
  Nonempty
      (xi_branch_register_image_coordinate_inverse_limit_cone ≃
        xi_branch_register_image_coordinate_inverse_limit_stream) ∧
    Function.Injective xi_branch_register_image_coordinate_inverse_limit_theta ∧
    Function.Surjective xi_branch_register_image_coordinate_inverse_limit_theta ∧
    ∀ s : xi_branch_register_image_coordinate_inverse_limit_stream, ∀ n : ℕ,
      xi_branch_register_image_coordinate_inverse_limit_prefix_right_shift n
          ((xi_branch_register_image_coordinate_inverse_limit_theta s).1 (n + 1)) =
        (xi_branch_register_image_coordinate_inverse_limit_theta
          (xi_branch_register_image_coordinate_inverse_limit_stream_right_shift s)).1 n

/-- Paper label: `thm:xi-branch-register-image-coordinate-inverse-limit`. -/
theorem paper_xi_branch_register_image_coordinate_inverse_limit :
    xi_branch_register_image_coordinate_inverse_limit_statement := by
  refine ⟨⟨xiPrimeRegisterInverseLimitEquiv Unit⟩, ?_, ?_, ?_⟩
  · intro s t hst
    calc
      s = xiPrimeRegisterToStream (xi_branch_register_image_coordinate_inverse_limit_theta s) := by
        simp [xi_branch_register_image_coordinate_inverse_limit_theta]
      _ = xiPrimeRegisterToStream (xi_branch_register_image_coordinate_inverse_limit_theta t) := by
        rw [hst]
      _ = t := by
        simp [xi_branch_register_image_coordinate_inverse_limit_theta]
  · intro F
    refine ⟨xiPrimeRegisterToStream F, ?_⟩
    simp [xi_branch_register_image_coordinate_inverse_limit_theta]
  · intro s n
    rfl

end Omega.Zeta
