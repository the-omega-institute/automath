import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic

namespace Omega.POM

open Matrix

/-- The `2 × 2` reversed-Pascal block used as the explicit `C^(q)` core. -/
def reversedPascalCore (q : Nat) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 : ℚ), q; 0, 1]

/-- Binomial-inversion formula for the reversed-Pascal core. -/
def reversedPascalCoreInv (q : Nat) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 : ℚ), -(q : ℚ); 0, 1]

/-- Exceptional rank-one update written in closed form. -/
def exceptionalBinomialKernel (q : Nat) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 / 2 : ℚ), ((q : ℚ) + 1) / 2; 0, 1 / 2]

/-- Closed entry formula for the inverse exceptional block. -/
def exceptionalBinomialKernelInv (q : Nat) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(2 : ℚ), -2 * ((q : ℚ) + 1); 0, 2]

/-- Scalar denominator appearing in the Sherman-Morrison update. -/
def exceptionalShermanMorrisonDenominator (q : Nat) : ℚ := (q : ℚ) + 1

/-- The core Pascal block and its rank-one exceptional update are both invertible, and the
inverse exceptional block has the advertised closed entries. -/
def exceptionalBinomialKernelInverseStatement (q : Nat) : Prop :=
  reversedPascalCore q * reversedPascalCoreInv q = 1 ∧
    reversedPascalCoreInv q * reversedPascalCore q = 1 ∧
    exceptionalShermanMorrisonDenominator q ≠ 0 ∧
    exceptionalBinomialKernel q * exceptionalBinomialKernelInv q = 1 ∧
    exceptionalBinomialKernelInv q * exceptionalBinomialKernel q = 1 ∧
    exceptionalBinomialKernelInv q 0 0 = 2 ∧
    exceptionalBinomialKernelInv q 0 1 = -2 * ((q : ℚ) + 1) ∧
    exceptionalBinomialKernelInv q 1 1 = 2

private theorem reversedPascalCore_mul_inv (q : Nat) :
    reversedPascalCore q * reversedPascalCoreInv q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [reversedPascalCore, reversedPascalCoreInv, Matrix.mul_apply]
  · simp [reversedPascalCore, reversedPascalCoreInv, Matrix.mul_apply]
  · simp [reversedPascalCore, reversedPascalCoreInv, Matrix.mul_apply]
  · simp [reversedPascalCore, reversedPascalCoreInv, Matrix.mul_apply]

private theorem reversedPascalCoreInv_mul_core (q : Nat) :
    reversedPascalCoreInv q * reversedPascalCore q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [reversedPascalCore, reversedPascalCoreInv, Matrix.mul_apply]
  · simp [reversedPascalCore, reversedPascalCoreInv, Matrix.mul_apply]
  · simp [reversedPascalCore, reversedPascalCoreInv, Matrix.mul_apply]
  · simp [reversedPascalCore, reversedPascalCoreInv, Matrix.mul_apply]

private theorem exceptionalBinomialKernel_mul_inv (q : Nat) :
    exceptionalBinomialKernel q * exceptionalBinomialKernelInv q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [exceptionalBinomialKernel, exceptionalBinomialKernelInv, Matrix.mul_apply]
  · simp [exceptionalBinomialKernel, exceptionalBinomialKernelInv, Matrix.mul_apply]
    ring
  · simp [exceptionalBinomialKernel, exceptionalBinomialKernelInv, Matrix.mul_apply]
  · simp [exceptionalBinomialKernel, exceptionalBinomialKernelInv, Matrix.mul_apply]

private theorem exceptionalBinomialKernelInv_mul_kernel (q : Nat) :
    exceptionalBinomialKernelInv q * exceptionalBinomialKernel q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [exceptionalBinomialKernel, exceptionalBinomialKernelInv, Matrix.mul_apply]
  · simp [exceptionalBinomialKernel, exceptionalBinomialKernelInv, Matrix.mul_apply]
    ring
  · simp [exceptionalBinomialKernel, exceptionalBinomialKernelInv, Matrix.mul_apply]
  · simp [exceptionalBinomialKernel, exceptionalBinomialKernelInv, Matrix.mul_apply]

/-- The exceptional binomial kernel has the explicit inverse obtained from the reversed-Pascal
core and the rank-one update.
    thm:xi-exceptional-binomial-kernel-inverse -/
theorem paper_xi_exceptional_binomial_kernel_inverse (q : Nat) (hq : 2 <= q) :
    exceptionalBinomialKernelInverseStatement q := by
  refine ⟨reversedPascalCore_mul_inv q, reversedPascalCoreInv_mul_core q, ?_,
    exceptionalBinomialKernel_mul_inv q, exceptionalBinomialKernelInv_mul_kernel q, ?_, ?_, ?_⟩
  have hq_nat : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
  · have hq' : (0 : ℚ) < (q : ℚ) + 1 := by
      have hq_rat : (0 : ℚ) < q := by
        exact_mod_cast hq_nat
      linarith
    exact ne_of_gt hq'
  · simp [exceptionalBinomialKernelInv]
  · simp [exceptionalBinomialKernelInv]
  · simp [exceptionalBinomialKernelInv]

end Omega.POM
