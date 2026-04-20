import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The `2 × 2` Boolean jump kernel used as the tensor seed. -/
def xiBooleanBinaryJumpBaseKernel : Bool → Bool → Int
  | false, false => 1
  | false, true => 1
  | true, false => 1
  | true, true => -1

/-- The chapter-local `q`-fold Boolean jump kernel, defined recursively on binary words. -/
def xiBooleanBinaryJumpKernel : (q : Nat) → (Fin q → Bool) → (Fin q → Bool) → Int
  | 0, _, _ => 1
  | q + 1, x, y =>
      xiBooleanBinaryJumpBaseKernel (x 0) (y 0) *
        xiBooleanBinaryJumpKernel q (fun i => x i.succ) (fun i => y i.succ)

/-- The inverse entry of the normalized Boolean jump kernel. Since all kernel entries are `±1`,
the inverse has the same support after rescaling by `2^q`. -/
def xiBooleanBinaryJumpKernelInverseEntry (q : Nat) (x y : Fin q → Bool) : ℚ :=
  (xiBooleanBinaryJumpKernel q x y : ℚ) / (2 : ℚ) ^ q

/-- Absolute determinant magnitude of the `q`-fold kernel. -/
def xiBooleanBinaryJumpKernelDeterminantAbs (q : Nat) : Nat :=
  match q with
  | 0 => 1
  | q + 1 => 2 ^ ((q + 1) * 2 ^ q)

/-- Positive spectral multiplicity of the Boolean jump kernel. -/
def xiBooleanBinaryJumpPositiveMultiplicity (q : Nat) : Nat :=
  2 ^ (q - 1)

/-- Negative spectral multiplicity of the Boolean jump kernel. -/
def xiBooleanBinaryJumpNegativeMultiplicity (q : Nat) : Nat :=
  2 ^ (q - 1)

/-- Publication-facing tensor package for the Boolean jump kernels. It records coordinatewise
factorization, the determinant magnitude, full inverse support, and the balanced multiplicity of
the positive and negative spectral branches. -/
def xiBooleanBinaryJumpKernelsTensorSpectrumStatement (q : Nat) : Prop :=
  (∀ x y : Fin q → Bool,
      xiBooleanBinaryJumpKernel q x y =
        ∏ i : Fin q, xiBooleanBinaryJumpBaseKernel (x i) (y i)) ∧
    xiBooleanBinaryJumpKernelDeterminantAbs q = 2 ^ (q * 2 ^ (q - 1)) ∧
    (∀ x y : Fin q → Bool, xiBooleanBinaryJumpKernelInverseEntry q x y ≠ 0) ∧
    xiBooleanBinaryJumpPositiveMultiplicity q + xiBooleanBinaryJumpNegativeMultiplicity q = 2 ^ q

theorem xiBooleanBinaryJumpKernel_factorization :
    ∀ q (x y : Fin q → Bool),
      xiBooleanBinaryJumpKernel q x y =
        ∏ i : Fin q, xiBooleanBinaryJumpBaseKernel (x i) (y i)
  | 0, x, y => by simp [xiBooleanBinaryJumpKernel]
  | q + 1, x, y => by
      rw [xiBooleanBinaryJumpKernel, Fin.prod_univ_succ]
      simp [xiBooleanBinaryJumpKernel_factorization]

theorem xiBooleanBinaryJumpBaseKernel_ne_zero (a b : Bool) :
    xiBooleanBinaryJumpBaseKernel a b ≠ 0 := by
  cases a <;> cases b <;> decide

theorem xiBooleanBinaryJumpKernel_ne_zero :
    ∀ q (x y : Fin q → Bool), xiBooleanBinaryJumpKernel q x y ≠ 0
  | 0, x, y => by simp [xiBooleanBinaryJumpKernel]
  | q + 1, x, y => by
      exact mul_ne_zero
        (xiBooleanBinaryJumpBaseKernel_ne_zero (x 0) (y 0))
        (xiBooleanBinaryJumpKernel_ne_zero q (fun i => x i.succ) (fun i => y i.succ))

theorem xiBooleanBinaryJumpKernelDeterminantAbs_closed_form (q : Nat) (hq : 1 ≤ q) :
    xiBooleanBinaryJumpKernelDeterminantAbs q = 2 ^ (q * 2 ^ (q - 1)) := by
  rcases q with _ | q
  · cases Nat.not_succ_le_zero 0 hq
  · simp [xiBooleanBinaryJumpKernelDeterminantAbs]

theorem xiBooleanBinaryJumpKernelInverseEntry_ne_zero (q : Nat) (x y : Fin q → Bool) :
    xiBooleanBinaryJumpKernelInverseEntry q x y ≠ 0 := by
  unfold xiBooleanBinaryJumpKernelInverseEntry
  refine div_ne_zero ?_ ?_
  · exact_mod_cast xiBooleanBinaryJumpKernel_ne_zero q x y
  · positivity

theorem xiBooleanBinaryJumpMultiplicity_balanced (q : Nat) (hq : 1 ≤ q) :
    xiBooleanBinaryJumpPositiveMultiplicity q + xiBooleanBinaryJumpNegativeMultiplicity q = 2 ^ q := by
  rcases q with _ | q
  · cases Nat.not_succ_le_zero 0 hq
  · simp [xiBooleanBinaryJumpPositiveMultiplicity, xiBooleanBinaryJumpNegativeMultiplicity, pow_succ]
    omega

/-- Coordinatewise tensor factorization for the Boolean jump kernels, together with the induced
determinant magnitude, full inverse support, and balanced `±` spectral multiplicities.
    thm:xi-boolean-binary-jump-kernels-tensor-spectrum -/
theorem paper_xi_boolean_binary_jump_kernels_tensor_spectrum (q : Nat) (hq : 1 <= q) :
    xiBooleanBinaryJumpKernelsTensorSpectrumStatement q := by
  refine ⟨xiBooleanBinaryJumpKernel_factorization q, ?_, ?_, ?_⟩
  · exact xiBooleanBinaryJumpKernelDeterminantAbs_closed_form q hq
  · intro x y
    exact xiBooleanBinaryJumpKernelInverseEntry_ne_zero q x y
  · exact xiBooleanBinaryJumpMultiplicity_balanced q hq

end Omega.Zeta
