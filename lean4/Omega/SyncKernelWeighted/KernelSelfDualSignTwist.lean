import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Omega.SyncKernelWeighted.KernelSelfDualCharacter

namespace Omega.SyncKernelWeighted

open Matrix

noncomputable section

/-- The sign-character specialization `B₋(u) = B₀ - u B₁`. -/
def kernel_self_dual_sign_twist_matrix {n : Type*} [Fintype n] [DecidableEq n] (u : ℂ)
    (B₀ B₁ : Matrix n n ℂ) : Matrix n n ℂ :=
  kernelCharacterTwist u (-1) B₀ B₁

/-- The determinant attached to the sign-twisted transfer matrix. -/
def kernel_self_dual_sign_twist_det {n : Type*} [Fintype n] [DecidableEq n] (z u : ℂ)
    (B₀ B₁ : Matrix n n ℂ) : ℂ :=
  kernelCharacterDet z u (-1) B₀ B₁

/-- The zeta factor attached to the sign-twisted transfer matrix. -/
def kernel_self_dual_sign_twist_zeta {n : Type*} [Fintype n] [DecidableEq n] (z u : ℂ)
    (B₀ B₁ : Matrix n n ℂ) : ℂ :=
  kernelCharacterZeta z u (-1) B₀ B₁

/-- The odd/asymmetric part `B_asym = (B₁ - B₀) / 2`. -/
def kernel_self_dual_sign_twist_odd_part {n : Type*} [Fintype n] [DecidableEq n]
    (B₀ B₁ : Matrix n n ℂ) : Matrix n n ℂ :=
  ((1 / 2 : ℂ)) • (B₁ - B₀)

/-- Publication-facing sign-character specialization of the self-dual kernel package. -/
def kernel_self_dual_sign_twist_statement : Prop :=
  ∀ {n : Type*} [Fintype n] [DecidableEq n], ∀ u z : ℂ,
    ∀ B₀ B₁ P : Matrix n n ℂ, IsUnit P.det → u ≠ 0 →
      P⁻¹ * B₀ * P = B₁ → P⁻¹ * B₁ * P = B₀ →
        P⁻¹ * kernel_self_dual_sign_twist_matrix u B₀ B₁ * P =
            (-u) • kernel_self_dual_sign_twist_matrix u⁻¹ B₀ B₁ ∧
          kernel_self_dual_sign_twist_det z u B₀ B₁ =
            kernel_self_dual_sign_twist_det ((-u) * z) u⁻¹ B₀ B₁ ∧
          kernel_self_dual_sign_twist_zeta z u B₀ B₁ =
            kernel_self_dual_sign_twist_zeta ((-u) * z) u⁻¹ B₀ B₁ ∧
          kernel_self_dual_sign_twist_matrix 1 B₀ B₁ =
            (-(2 : ℂ)) • kernel_self_dual_sign_twist_odd_part B₀ B₁

/-- Paper label: `cor:kernel-self-dual-sign-twist`. Specializing the existing self-dual
character theorem to `χ(g₁) = -1` gives the signed similarity/determinant/zeta functional
equations, and at `u = 1` the sign-twisted channel reads off exactly the odd part. -/
theorem paper_kernel_self_dual_sign_twist : kernel_self_dual_sign_twist_statement := by
  intro n _ _ u z B₀ B₁ P hP hu hB₀ hB₁
  have hbase :=
    paper_kernel_self_dual_character (n := n) u (-1 : ℂ) z B₀ B₁ P hP hu (by norm_num) hB₀ hB₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [kernel_self_dual_sign_twist_matrix, mul_comm, mul_left_comm, mul_assoc] using hbase.1
  · simpa [kernel_self_dual_sign_twist_det, mul_comm, mul_left_comm, mul_assoc] using hbase.2.1
  · simpa [kernel_self_dual_sign_twist_zeta, mul_comm, mul_left_comm, mul_assoc] using hbase.2.2
  · ext i j
    simp [kernel_self_dual_sign_twist_matrix, kernel_self_dual_sign_twist_odd_part,
      kernelCharacterTwist]
    ring

end

end Omega.SyncKernelWeighted
