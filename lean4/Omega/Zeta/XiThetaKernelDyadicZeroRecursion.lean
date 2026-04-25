import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiThetaKernelDyadicDecompositionDoubleexpTail

namespace Omega.Zeta

/-- Concrete data for the dyadic theta-kernel zero recursion package. The dyadic shell completion
provides the perturbative error term, `γ` is the reference simple zero, and `x₀` is the current
Newton seed. -/
structure xi_theta_kernel_dyadic_zero_recursion_data where
  xi_theta_kernel_dyadic_zero_recursion_K : ℕ
  xi_theta_kernel_dyadic_zero_recursion_C : ℝ
  xi_theta_kernel_dyadic_zero_recursion_t : ℝ
  xi_theta_kernel_dyadic_zero_recursion_gamma : ℝ
  xi_theta_kernel_dyadic_zero_recursion_x0 : ℝ
  xi_theta_kernel_dyadic_zero_recursion_C_nonneg :
    0 ≤ xi_theta_kernel_dyadic_zero_recursion_C

namespace xi_theta_kernel_dyadic_zero_recursion_data

/-- The dyadic completion error inherited from the shell model. -/
noncomputable def xi_theta_kernel_dyadic_zero_recursion_tail
    (D : xi_theta_kernel_dyadic_zero_recursion_data) : ℝ :=
  xi_theta_kernel_dyadic_decomposition_doubleexp_tail_completion
      D.xi_theta_kernel_dyadic_zero_recursion_C
      D.xi_theta_kernel_dyadic_zero_recursion_t
      D.xi_theta_kernel_dyadic_zero_recursion_K -
    xi_theta_kernel_dyadic_decomposition_doubleexp_tail_partial
      D.xi_theta_kernel_dyadic_zero_recursion_C
      D.xi_theta_kernel_dyadic_zero_recursion_t
      D.xi_theta_kernel_dyadic_zero_recursion_K

/-- Explicit control radius from the dyadic tail theorem. -/
noncomputable def xi_theta_kernel_dyadic_zero_recursion_controlRadius
    (D : xi_theta_kernel_dyadic_zero_recursion_data) : ℝ :=
  xi_theta_kernel_dyadic_decomposition_doubleexp_tail_constant *
    D.xi_theta_kernel_dyadic_zero_recursion_C *
      xi_theta_kernel_dyadic_decomposition_doubleexp_tail_weight
        D.xi_theta_kernel_dyadic_zero_recursion_K

/-- The remainder term `H_K`. In this concrete affine model it is the dyadic completion error. -/
noncomputable def xi_theta_kernel_dyadic_zero_recursion_H_K
    (D : xi_theta_kernel_dyadic_zero_recursion_data) (_x : ℝ) : ℝ :=
  D.xi_theta_kernel_dyadic_zero_recursion_tail

/-- The local zero-tracking model `F_K(x) = (x - γ) + H_K(x)`. -/
noncomputable def xi_theta_kernel_dyadic_zero_recursion_F_K
    (D : xi_theta_kernel_dyadic_zero_recursion_data) (x : ℝ) : ℝ :=
  x - D.xi_theta_kernel_dyadic_zero_recursion_gamma +
    D.xi_theta_kernel_dyadic_zero_recursion_H_K x

/-- The unique zero of the affine dyadic model. -/
noncomputable def xi_theta_kernel_dyadic_zero_recursion_root
    (D : xi_theta_kernel_dyadic_zero_recursion_data) : ℝ :=
  D.xi_theta_kernel_dyadic_zero_recursion_gamma -
    D.xi_theta_kernel_dyadic_zero_recursion_tail

/-- One Newton-style update for the affine dyadic model. -/
noncomputable def xi_theta_kernel_dyadic_zero_recursion_newtonStep
    (D : xi_theta_kernel_dyadic_zero_recursion_data) (x : ℝ) : ℝ :=
  x - D.xi_theta_kernel_dyadic_zero_recursion_F_K x

/-- Paper-facing statement for the concrete dyadic zero recursion package. -/
def xi_theta_kernel_dyadic_zero_recursion_holds
    (D : xi_theta_kernel_dyadic_zero_recursion_data) : Prop :=
  (∀ x,
    D.xi_theta_kernel_dyadic_zero_recursion_F_K x =
      x - D.xi_theta_kernel_dyadic_zero_recursion_gamma +
        D.xi_theta_kernel_dyadic_zero_recursion_H_K x) ∧
  |D.xi_theta_kernel_dyadic_zero_recursion_tail| ≤
    D.xi_theta_kernel_dyadic_zero_recursion_controlRadius ∧
  D.xi_theta_kernel_dyadic_zero_recursion_F_K
      (D.xi_theta_kernel_dyadic_zero_recursion_gamma -
        D.xi_theta_kernel_dyadic_zero_recursion_controlRadius) ≤ 0 ∧
  0 ≤
    D.xi_theta_kernel_dyadic_zero_recursion_F_K
      (D.xi_theta_kernel_dyadic_zero_recursion_gamma +
        D.xi_theta_kernel_dyadic_zero_recursion_controlRadius) ∧
  (∀ x y,
    x < y →
      D.xi_theta_kernel_dyadic_zero_recursion_F_K x <
        D.xi_theta_kernel_dyadic_zero_recursion_F_K y) ∧
  ∃! ξ,
    |ξ - D.xi_theta_kernel_dyadic_zero_recursion_gamma| ≤
      D.xi_theta_kernel_dyadic_zero_recursion_controlRadius ∧
    D.xi_theta_kernel_dyadic_zero_recursion_F_K ξ = 0 ∧
    D.xi_theta_kernel_dyadic_zero_recursion_newtonStep
        D.xi_theta_kernel_dyadic_zero_recursion_x0 = ξ ∧
    |D.xi_theta_kernel_dyadic_zero_recursion_newtonStep
          D.xi_theta_kernel_dyadic_zero_recursion_x0 - ξ| ≤
      |D.xi_theta_kernel_dyadic_zero_recursion_x0 - ξ| ^ 2

end xi_theta_kernel_dyadic_zero_recursion_data

open xi_theta_kernel_dyadic_zero_recursion_data

/-- Paper label: `thm:xi-theta-kernel-dyadic-zero-recursion`. The dyadic shell completion controls
an explicit affine theta-kernel model whose zero remains in the tail window, is unique by strict
monotonicity, and is recovered exactly by one Newton update, yielding the stated quadratic error
bound. -/
theorem paper_xi_theta_kernel_dyadic_zero_recursion
    (D : xi_theta_kernel_dyadic_zero_recursion_data) :
    D.xi_theta_kernel_dyadic_zero_recursion_holds := by
  have htail :=
    (paper_xi_theta_kernel_dyadic_decomposition_doubleexp_tail
      D.xi_theta_kernel_dyadic_zero_recursion_C
      D.xi_theta_kernel_dyadic_zero_recursion_t
      D.xi_theta_kernel_dyadic_zero_recursion_K
      D.xi_theta_kernel_dyadic_zero_recursion_C_nonneg).2.2
  have htail' :
      |D.xi_theta_kernel_dyadic_zero_recursion_tail| ≤
        D.xi_theta_kernel_dyadic_zero_recursion_controlRadius := by
    simpa [xi_theta_kernel_dyadic_zero_recursion_tail,
      xi_theta_kernel_dyadic_zero_recursion_controlRadius] using htail
  have hsplit :
      -D.xi_theta_kernel_dyadic_zero_recursion_controlRadius ≤
          D.xi_theta_kernel_dyadic_zero_recursion_tail ∧
        D.xi_theta_kernel_dyadic_zero_recursion_tail ≤
          D.xi_theta_kernel_dyadic_zero_recursion_controlRadius := by
    exact abs_le.mp htail'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · exact htail'
  · unfold xi_theta_kernel_dyadic_zero_recursion_F_K
      xi_theta_kernel_dyadic_zero_recursion_H_K
    linarith [hsplit.2]
  · unfold xi_theta_kernel_dyadic_zero_recursion_F_K
      xi_theta_kernel_dyadic_zero_recursion_H_K
    linarith [hsplit.1]
  · intro x y hxy
    unfold xi_theta_kernel_dyadic_zero_recursion_F_K
      xi_theta_kernel_dyadic_zero_recursion_H_K
    linarith
  · refine ⟨D.xi_theta_kernel_dyadic_zero_recursion_root, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · have hroot :
            D.xi_theta_kernel_dyadic_zero_recursion_root -
                D.xi_theta_kernel_dyadic_zero_recursion_gamma =
              -D.xi_theta_kernel_dyadic_zero_recursion_tail := by
          unfold xi_theta_kernel_dyadic_zero_recursion_root
          ring
        rw [hroot, abs_neg]
        exact htail'
      · unfold xi_theta_kernel_dyadic_zero_recursion_F_K
          xi_theta_kernel_dyadic_zero_recursion_H_K
          xi_theta_kernel_dyadic_zero_recursion_root
        ring
      · have hnext :
            D.xi_theta_kernel_dyadic_zero_recursion_newtonStep
                D.xi_theta_kernel_dyadic_zero_recursion_x0 =
              D.xi_theta_kernel_dyadic_zero_recursion_root := by
          unfold xi_theta_kernel_dyadic_zero_recursion_newtonStep
            xi_theta_kernel_dyadic_zero_recursion_F_K
            xi_theta_kernel_dyadic_zero_recursion_H_K
            xi_theta_kernel_dyadic_zero_recursion_root
          ring
        refine ⟨hnext, ?_⟩
        rw [hnext]
        have hsquare_nonneg :
            0 ≤
              |D.xi_theta_kernel_dyadic_zero_recursion_x0 -
                  D.xi_theta_kernel_dyadic_zero_recursion_root| ^ 2 := by
          positivity
        simpa using hsquare_nonneg
    · intro ξ hξ
      have hzero : D.xi_theta_kernel_dyadic_zero_recursion_F_K ξ = 0 := hξ.2.1
      change ξ =
        D.xi_theta_kernel_dyadic_zero_recursion_gamma -
          D.xi_theta_kernel_dyadic_zero_recursion_tail
      unfold xi_theta_kernel_dyadic_zero_recursion_F_K
        xi_theta_kernel_dyadic_zero_recursion_H_K at hzero
      linarith

end Omega.Zeta
