import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.ZMod.Basic
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

/-- Integer shadow of the exceptional first-row inverse coefficients. The first coordinate keeps
the visible factor `2`, while the off-diagonal term remains an even multiple, so the image is
detected exactly by the parity of the first output coordinate. -/
def xiExceptionalBinomialKernelInt (q : ℕ) (x : Fin 2 → ℤ) : Fin 2 → ℤ
  | 0 => 2 * x 0 - (2 * ((q : ℤ) + 1)) * x 1
  | 1 => x 1

/-- The mod-`2` reduction of the integer shadow. -/
def xiExceptionalBinomialKernelMod2 (_q : ℕ) (x : Fin 2 → ZMod 2) : Fin 2 → ZMod 2
  | 0 => 0
  | 1 => x 1

/-- The distinguished generator of the mod-`2` kernel. -/
def xiExceptionalE0Mod2 : Fin 2 → ZMod 2
  | 0 => 1
  | 1 => 0

/-- The mod-`2` kernel consists exactly of the two points on the `e₀` line. -/
def xiExceptionalMod2KernelIsSpanE0 (q : ℕ) : Prop :=
  ∀ x : Fin 2 → ZMod 2, xiExceptionalBinomialKernelMod2 q x = 0 ↔ x = 0 ∨ x = xiExceptionalE0Mod2

/-- Paper label: `prop:xi-exceptional-binomial-kernel-image-cokernel`.
The integer image has index `2`, detected by the parity of the first coordinate, and after
reducing mod `2` the kernel is exactly the `e₀`-line. -/
theorem paper_xi_exceptional_binomial_kernel_image_cokernel (q : ℕ) (hq : 2 ≤ q) :
    (∀ y : Fin 2 → ℤ, (∃ x : Fin 2 → ℤ, xiExceptionalBinomialKernelInt q x = y) ↔
      Even (y 0)) ∧
      xiExceptionalMod2KernelIsSpanE0 q := by
  let _ := paper_xi_exceptional_binomial_kernel_inverse q hq
  refine ⟨?_, ?_⟩
  · intro y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x 0 - ((q : ℤ) + 1) * x 1, by
        simp [xiExceptionalBinomialKernelInt]
        ring⟩
    · rintro ⟨k, hk⟩
      refine ⟨fun i => if i = 0 then k + ((q : ℤ) + 1) * y 1 else y 1, ?_⟩
      ext i
      fin_cases i
      · simp [xiExceptionalBinomialKernelInt, hk]
        ring
      · simp [xiExceptionalBinomialKernelInt]
  · intro x
    constructor
    · intro hx
      have hx1 : x 1 = 0 := by
        have := congrArg (fun f => f 1) hx
        simpa [xiExceptionalBinomialKernelMod2] using this
      have hx0_cases : x 0 = 0 ∨ x 0 = 1 := by
        have hclassified : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
          intro a
          fin_cases a <;> simp
        exact hclassified (x 0)
      rcases hx0_cases with hx0 | hx0
      · left
        ext i
        fin_cases i <;> simp [hx0, hx1]
      · right
        ext i
        fin_cases i <;> simp [xiExceptionalE0Mod2, hx0, hx1]
    · rintro (rfl | rfl)
      · ext i
        fin_cases i <;> simp [xiExceptionalBinomialKernelMod2]
      · ext i
        fin_cases i <;> simp [xiExceptionalBinomialKernelMod2, xiExceptionalE0Mod2]

end Omega.POM
