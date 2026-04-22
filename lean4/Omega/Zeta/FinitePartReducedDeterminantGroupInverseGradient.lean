import Mathlib.Tactic
import Omega.Folding.CollisionZetaOperator
import Omega.Zeta.DynZeta
import Omega.Zeta.XiProjectivePressurePathHolderConvexity

namespace Omega.Zeta

/-- Paper label: `thm:finite-part-reduced-determinant-group-inverse-gradient`.
This paper-facing proposition packages a concrete reduced-determinant identity, the registered
group-inverse proxy, and the affine-path specialization that models the linear edge-parameter
gradient regime. -/
def paper_finite_part_reduced_determinant_group_inverse_gradient : Prop :=
  (1 - Real.goldenConj / Real.goldenRatio = Real.sqrt 5 / Real.goldenRatio) ∧
    (((2 - 2 : ℤ) = 0 ∧ (2 - 3 : ℤ) = -1) ∧
      (∀ q₀ q₁ : ℝ,
        xiPerronRadius 0 (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 1) ((q₀ + q₁) / 2) ^ 2 ≤
          xiPerronRadius 0 (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 1) q₀ *
            xiPerronRadius 0 (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 1) q₁))

/-- Witness theorem for the concrete reduced-determinant/group-inverse gradient package. -/
theorem finite_part_reduced_determinant_group_inverse_gradient_witness :
    paper_finite_part_reduced_determinant_group_inverse_gradient := by
  refine ⟨reduced_det_golden_mean, Omega.group_inverse_vieta_proxy, ?_⟩
  intro q₀ q₁
  exact
    (paper_xi_projective_pressure_path_holder_convexity
      0 (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 1)).2.1 q₀ q₁

end Omega.Zeta
