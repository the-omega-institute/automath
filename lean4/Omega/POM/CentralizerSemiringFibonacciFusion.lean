import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega

open Matrix

/-- The nonnegative golden-mean transfer matrix, written over `Nat`.
It is the semiring version of `Omega.Graph.goldenMeanAdjacency`. -/
def goldenMeanAdjacencyNat : Matrix (Fin 2) (Fin 2) Nat :=
  !![(1 : Nat), 1; 1, 0]

/-- The concrete fusion rule `M^2 = M + I` for the `Nat`-valued golden matrix. -/
theorem goldenMeanAdjacencyNat_sq :
    goldenMeanAdjacencyNat ^ 2 = goldenMeanAdjacencyNat + 1 := by
  native_decide

/-- Paper label: `thm:pom-centralizer-semiring-fibonacci-fusion`.
For the `Nat`-valued golden matrix, every commuting `2 × 2` matrix is of the form `a I + b M`. -/
theorem paper_pom_centralizer_semiring_fibonacci_fusion :
    ∀ A : Matrix (Fin 2) (Fin 2) Nat,
      A * goldenMeanAdjacencyNat = goldenMeanAdjacencyNat * A ->
      ∃ a b : Nat, A = a • (1 : Matrix (Fin 2) (Fin 2) Nat) + b • goldenMeanAdjacencyNat := by
  intro A hcomm
  let p := A 0 0
  let q := A 0 1
  let r := A 1 0
  let s := A 1 1
  have hrq : r = q := by
    have h := congr_fun (congr_fun hcomm 1) 1
    simp [goldenMeanAdjacencyNat, Matrix.mul_apply, Fin.sum_univ_two] at h
    exact h
  have hps : p = q + s := by
    have h := congr_fun (congr_fun hcomm 1) 0
    simp [goldenMeanAdjacencyNat, Matrix.mul_apply, Fin.sum_univ_two] at h
    omega
  have hform : A = !![q + s, q; q, s] := by
    ext i j <;> fin_cases i <;> fin_cases j
    · simpa [p] using hps
    · simp [q]
    · simpa [r] using hrq
    · simp [s]
  refine ⟨s, q, hform.trans ?_⟩
  calc
    !![q + s, q; q, s] = (s : Matrix (Fin 2) (Fin 2) Nat) + q • goldenMeanAdjacencyNat := by
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [goldenMeanAdjacencyNat, Matrix.natCast_apply, Nat.add_comm]
    _ = s • (1 : Matrix (Fin 2) (Fin 2) Nat) + q • goldenMeanAdjacencyNat := by
      have hs : (s : Matrix (Fin 2) (Fin 2) Nat) = s • (1 : Matrix (Fin 2) (Fin 2) Nat) := by
        rw [nsmul_eq_mul, mul_one]
      rw [hs]

end Omega
