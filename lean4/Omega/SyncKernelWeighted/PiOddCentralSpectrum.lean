import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Omega.SyncKernelWeighted.KernelSelfDualSignTwist

namespace Omega.SyncKernelWeighted

open Matrix

noncomputable section

/-- Central-spectrum symmetry package for the odd/sign-twisted slice at `u = 1`. -/
def pi_odd_central_spectrum_statement : Prop :=
  ∀ {n : Type*} [Fintype n] [DecidableEq n], ∀ z : ℂ,
    ∀ B₀ B₁ P : Matrix n n ℂ, IsUnit P.det →
      P⁻¹ * B₀ * P = B₁ → P⁻¹ * B₁ * P = B₀ →
        P⁻¹ * kernel_self_dual_sign_twist_odd_part B₀ B₁ * P =
            (-1 : ℂ) • kernel_self_dual_sign_twist_odd_part B₀ B₁ ∧
          kernel_self_dual_sign_twist_det z 1 B₀ B₁ =
            kernel_self_dual_sign_twist_det (-z) 1 B₀ B₁ ∧
          (kernel_self_dual_sign_twist_det z 1 B₀ B₁ = 0 ↔
            kernel_self_dual_sign_twist_det (-z) 1 B₀ B₁ = 0)

/-- Paper label: `prop:pi-odd-central-spectrum`. The sign-twist package identifies the odd slice at
`u = 1`; its similarity to the negative odd part forces the determinant to be even in `z`, so the
central spectrum is symmetric under `z ↦ -z`. -/
theorem paper_pi_odd_central_spectrum : pi_odd_central_spectrum_statement := by
  intro n _ _ z B₀ B₁ P hP hB₀ hB₁
  have hsign :=
    paper_kernel_self_dual_sign_twist (n := n) (u := 1) (z := z) B₀ B₁ P hP one_ne_zero hB₀ hB₁
  have hodd :
      P⁻¹ * kernel_self_dual_sign_twist_odd_part B₀ B₁ * P =
        (-1 : ℂ) • kernel_self_dual_sign_twist_odd_part B₀ B₁ := by
    calc
      P⁻¹ * kernel_self_dual_sign_twist_odd_part B₀ B₁ * P
          = ((1 / 2 : ℂ)) • (P⁻¹ * (B₁ - B₀) * P) := by
              simp [kernel_self_dual_sign_twist_odd_part, Matrix.mul_sub, Matrix.sub_mul,
                Matrix.mul_assoc]
      _ = ((1 / 2 : ℂ)) • (B₀ - B₁) := by
            simp [Matrix.mul_sub, Matrix.sub_mul, hB₀, hB₁]
      _ = (-1 : ℂ) • kernel_self_dual_sign_twist_odd_part B₀ B₁ := by
            ext i j
            simp [kernel_self_dual_sign_twist_odd_part]
            ring
  have hdet :
      kernel_self_dual_sign_twist_det z 1 B₀ B₁ =
        kernel_self_dual_sign_twist_det (-z) 1 B₀ B₁ := by
    simpa using hsign.2.1
  refine ⟨hodd, hdet, ?_⟩
  constructor <;> intro hz0
  · rw [hdet] at hz0
    exact hz0
  · rw [hdet]
    exact hz0

end

end Omega.SyncKernelWeighted
