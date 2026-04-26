import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Matrix

/-- Completed `2 × 2` seed used for the Ward-trace parity calculation. -/
def witt_dieudonne_dwork_completed (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, θ; -θ, 1]

/-- Involution implementing the completed similarity `θ ↦ -θ`. -/
def witt_dieudonne_dwork_pi : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- Odd part of the completed seed at `θ = 0`. -/
def witt_dieudonne_dwork_B_asym : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -1, 0]

lemma witt_dieudonne_dwork_pi_sq :
    witt_dieudonne_dwork_pi * witt_dieudonne_dwork_pi = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [witt_dieudonne_dwork_pi, Matrix.mul_apply]

lemma witt_dieudonne_dwork_similarity (θ : ℝ) :
    witt_dieudonne_dwork_completed (-θ) =
      witt_dieudonne_dwork_pi * witt_dieudonne_dwork_completed θ * witt_dieudonne_dwork_pi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witt_dieudonne_dwork_completed, witt_dieudonne_dwork_pi, Matrix.mul_apply]

lemma witt_dieudonne_dwork_completed_zero :
    witt_dieudonne_dwork_completed 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [witt_dieudonne_dwork_completed]

lemma witt_dieudonne_dwork_similarity_pow (θ : ℝ) (n : ℕ) :
    (witt_dieudonne_dwork_pi * witt_dieudonne_dwork_completed θ * witt_dieudonne_dwork_pi) ^ n =
      witt_dieudonne_dwork_pi * (witt_dieudonne_dwork_completed θ) ^ n * witt_dieudonne_dwork_pi := by
  let A := witt_dieudonne_dwork_completed θ
  let P := witt_dieudonne_dwork_pi
  have hP : P * P = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    simpa [P] using witt_dieudonne_dwork_pi_sq
  induction n with
  | zero =>
      simp [P, hP]
  | succ n ih =>
      calc
        (P * A * P) ^ (n + 1) = (P * A * P) ^ n * (P * A * P) := by
          simp [pow_succ]
        _ = (P * A ^ n * P) * (P * A * P) := by
          rw [ih]
        _ = P * A ^ n * (P * P) * A * P := by
          simp [Matrix.mul_assoc]
        _ = P * A ^ n * 1 * A * P := by
          rw [hP]
        _ = P * (A ^ n * A) * P := by
          simp [Matrix.mul_assoc]
        _ = P * A ^ (n + 1) * P := by
          simp [pow_succ, Matrix.mul_assoc]
        _ = witt_dieudonne_dwork_pi * (witt_dieudonne_dwork_completed θ) ^ (n + 1) *
              witt_dieudonne_dwork_pi := by
          simp [A, P]

lemma witt_dieudonne_dwork_trace_pow_even (n : ℕ) (θ : ℝ) :
    Matrix.trace ((witt_dieudonne_dwork_completed (-θ)) ^ n) =
      Matrix.trace ((witt_dieudonne_dwork_completed θ) ^ n) := by
  calc
    Matrix.trace ((witt_dieudonne_dwork_completed (-θ)) ^ n) =
        Matrix.trace
          ((witt_dieudonne_dwork_pi * witt_dieudonne_dwork_completed θ *
              witt_dieudonne_dwork_pi) ^ n) := by
            rw [witt_dieudonne_dwork_similarity]
    _ = Matrix.trace
          (witt_dieudonne_dwork_pi * (witt_dieudonne_dwork_completed θ) ^ n *
            witt_dieudonne_dwork_pi) := by
            rw [witt_dieudonne_dwork_similarity_pow]
    _ = Matrix.trace
          (witt_dieudonne_dwork_pi * witt_dieudonne_dwork_pi *
            (witt_dieudonne_dwork_completed θ) ^ n) := by
            simpa [Matrix.mul_assoc] using
              (Matrix.trace_mul_cycle witt_dieudonne_dwork_pi
                ((witt_dieudonne_dwork_completed θ) ^ n) witt_dieudonne_dwork_pi)
    _ = Matrix.trace (1 * (witt_dieudonne_dwork_completed θ) ^ n) := by
            rw [witt_dieudonne_dwork_pi_sq]
    _ = Matrix.trace ((witt_dieudonne_dwork_completed θ) ^ n) := by simp

/-- Paper label: `lem:witt-dieudonne-dwork`. The completed `2 × 2` seed is conjugate to its
`θ ↦ -θ` reflection by the involution `Π`, so every trace power is even in `θ`. At `θ = 0` the
linearized odd part is the traceless antisymmetric block `B_asym`, hence the cyclic trace
expansion vanishes. -/
theorem paper_witt_dieudonne_dwork (n : ℕ) :
    (∀ θ : ℝ,
      Matrix.trace ((witt_dieudonne_dwork_completed (-θ)) ^ n) =
        Matrix.trace ((witt_dieudonne_dwork_completed θ) ^ n)) ∧
      (Matrix.trace
        (Finset.sum (Finset.range n) fun k =>
          (witt_dieudonne_dwork_completed 0) ^ k * witt_dieudonne_dwork_B_asym *
            (witt_dieudonne_dwork_completed 0) ^ (n - 1 - k)) = 0) := by
  refine ⟨witt_dieudonne_dwork_trace_pow_even n, ?_⟩
  have hterm :
      ∀ k ∈ Finset.range n,
        (witt_dieudonne_dwork_completed 0) ^ k * witt_dieudonne_dwork_B_asym *
            (witt_dieudonne_dwork_completed 0) ^ (n - 1 - k) =
          witt_dieudonne_dwork_B_asym := by
    intro k hk
    rw [witt_dieudonne_dwork_completed_zero]
    simp [witt_dieudonne_dwork_B_asym]
  calc
    Matrix.trace
        (Finset.sum (Finset.range n) fun k =>
          (witt_dieudonne_dwork_completed 0) ^ k * witt_dieudonne_dwork_B_asym *
            (witt_dieudonne_dwork_completed 0) ^ (n - 1 - k)) =
        Matrix.trace (Finset.sum (Finset.range n) fun _ => witt_dieudonne_dwork_B_asym) := by
          refine congrArg Matrix.trace ?_
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact hterm k hk
    _ = 0 := by
        simp [witt_dieudonne_dwork_B_asym, Matrix.trace, Fin.sum_univ_two]

/-- Paper label: `lem:sync-kernel-ward-traces`. In the concrete completed `2 × 2` seed, the
first-order Ward trace vanishes for every time length because `\widetilde B(0) = I` and the odd
part is traceless. -/
theorem paper_sync_kernel_ward_traces :
    ∀ n : ℕ, 1 ≤ n →
      Matrix.trace ((witt_dieudonne_dwork_completed 0) ^ (n - 1) * witt_dieudonne_dwork_B_asym) =
        0 := by
  intro n hn
  rw [witt_dieudonne_dwork_completed_zero]
  simp [witt_dieudonne_dwork_B_asym, Matrix.trace, Fin.sum_univ_two]

end Omega.SyncKernelWeighted
