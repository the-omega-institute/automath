import Mathlib.Analysis.Complex.Norm
import Omega.Zeta.XiDepthHankelDeterminantVandermondeSquare

namespace Omega.Zeta

open scoped BigOperators

/-- The radial height of a finite atomic scan node, embedded back into `ℂ`. -/
noncomputable def xi_scan_depth_height_tensor_factorization_height {κ : Nat}
    (D : XiFiniteAtomicMomentData κ) (j : Fin κ) : ℂ :=
  (‖D.nodes j‖ : ℝ)

/-- The unit-phase carrier of a finite atomic scan node, with phase `1` at the zero node. -/
noncomputable def xi_scan_depth_height_tensor_factorization_phase {κ : Nat}
    (D : XiFiniteAtomicMomentData κ) (j : Fin κ) : ℂ :=
  if D.nodes j = 0 then 1 else
    D.nodes j / xi_scan_depth_height_tensor_factorization_height D j

/-- Concrete depth/height tensor split of the finite atomic moment model. -/
def xi_scan_depth_height_tensor_factorization_statement
    (κ : Nat) (D : XiFiniteAtomicMomentData κ) : Prop :=
  ∀ n : Nat,
    D.moments n =
      ∑ j : Fin κ,
        D.weights j *
          xi_scan_depth_height_tensor_factorization_height D j ^ n *
            xi_scan_depth_height_tensor_factorization_phase D j ^ n

lemma xi_scan_depth_height_tensor_factorization_node_eq_height_mul_phase {κ : Nat}
    (D : XiFiniteAtomicMomentData κ) (j : Fin κ) :
    D.nodes j =
      xi_scan_depth_height_tensor_factorization_height D j *
        xi_scan_depth_height_tensor_factorization_phase D j := by
  by_cases hz : D.nodes j = 0
  · simp [xi_scan_depth_height_tensor_factorization_height,
      xi_scan_depth_height_tensor_factorization_phase, hz]
  · have hnorm_ne : (‖D.nodes j‖ : ℝ) ≠ 0 := by
      simpa [norm_eq_zero] using hz
    have hheight_ne :
        xi_scan_depth_height_tensor_factorization_height D j ≠ 0 := by
      simpa [xi_scan_depth_height_tensor_factorization_height] using
        (Complex.ofReal_ne_zero.mpr hnorm_ne)
    rw [xi_scan_depth_height_tensor_factorization_phase, if_neg hz, div_eq_mul_inv]
    calc
      D.nodes j =
          D.nodes j *
            (xi_scan_depth_height_tensor_factorization_height D j *
              (xi_scan_depth_height_tensor_factorization_height D j)⁻¹) := by
        simp [hheight_ne]
      _ =
          xi_scan_depth_height_tensor_factorization_height D j *
            (D.nodes j * (xi_scan_depth_height_tensor_factorization_height D j)⁻¹) := by
        ring

/-- Paper label: `prop:xi-scan-depth-height-tensor-factorization`. The finite atomic moments split
node powers into radial heights and phase carriers by multiplicativity of powers. -/
theorem paper_xi_scan_depth_height_tensor_factorization (κ : Nat)
    (D : XiFiniteAtomicMomentData κ) :
    xi_scan_depth_height_tensor_factorization_statement κ D := by
  intro n
  rw [D.moments_eq n]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hnode := xi_scan_depth_height_tensor_factorization_node_eq_height_mul_phase D j
  calc
    D.weights j * D.nodes j ^ n =
        D.weights j *
          (xi_scan_depth_height_tensor_factorization_height D j *
            xi_scan_depth_height_tensor_factorization_phase D j) ^ n := by
          rw [hnode]
    _ = D.weights j *
          xi_scan_depth_height_tensor_factorization_height D j ^ n *
            xi_scan_depth_height_tensor_factorization_phase D j ^ n := by
          rw [mul_pow]
          ring

end Omega.Zeta
