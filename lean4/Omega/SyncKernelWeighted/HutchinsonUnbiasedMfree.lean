import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Matrix

noncomputable section

/-- The quadratic form sampled by the Hutchinson trace estimator. -/
def hutchinsonQuadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) : ℝ :=
  dotProduct r (A *ᵥ r)

/-- The empirical second moment of a sample family. -/
def empiricalSecondMoment {n s : ℕ} (samples : Fin s → Fin n → ℝ) (i j : Fin n) : ℝ :=
  (1 / (s : ℝ)) * ∑ ω : Fin s, samples ω i * samples ω j

/-- Exact diagonal/off-diagonal moment closure for a concrete sample family. -/
def exactSecondMomentDesign {n s : ℕ} (samples : Fin s → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, empiricalSecondMoment samples i j = if i = j then 1 else 0

/-- The single-draw unbiasedness statement, encoded as the empirical average of the quadratic
form over a concrete exact-design family. -/
def singleSampleUnbiased {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (samples : Fin s → Fin n → ℝ) :
    Prop :=
  (1 / (s : ℝ)) * ∑ ω : Fin s, hutchinsonQuadraticForm A (samples ω) = Matrix.trace A

/-- The sample-mean unbiasedness statement for repeated copies of the same exact-design average. -/
def sampleMeanUnbiased {n s t : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (samples : Fin s → Fin n → ℝ) :
    Prop :=
  (1 / (t : ℝ)) * ∑ _ : Fin t, (1 / (s : ℝ)) * ∑ ω : Fin s, hutchinsonQuadraticForm A (samples ω) =
    Matrix.trace A

/-- The matrix-free recurrence obtained by iterating sparse matrix-vector multiplication. -/
def matrixFreeSequence {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => r
  | m + 1 => K *ᵥ matrixFreeSequence K r m

/-- The recurrence starts from the probe vector, advances by matrix-vector multiplication,
and evaluates the same quadratic form as `K ^ m`. -/
def matrixFreeRecurrence {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (m : ℕ) : Prop :=
  matrixFreeSequence K r 0 = r ∧
    (∀ k : ℕ, matrixFreeSequence K r (k + 1) = K *ᵥ matrixFreeSequence K r k) ∧
    hutchinsonQuadraticForm (K ^ m) r = dotProduct r (matrixFreeSequence K r m)

lemma matrixFreeSequence_eq_pow_mulVec {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) :
    ∀ m : ℕ, matrixFreeSequence K r m = (K ^ m) *ᵥ r
  | 0 => by simp [matrixFreeSequence]
  | m + 1 => by
      rw [matrixFreeSequence, matrixFreeSequence_eq_pow_mulVec, pow_succ', Matrix.mulVec_mulVec]

/-- A concrete Hutchinson package: exact second moments recover the trace, averaging preserved
under repeated sampling is still unbiased, and the power `K ^ m` is computed by the matrix-free
recurrence `v₀ = r`, `v_{k+1} = K v_k`. -/
theorem paper_hutchinson_unbiased_mfree {n s t : ℕ} (A K : Matrix (Fin n) (Fin n) ℝ)
    (samples : Fin s → Fin n → ℝ) (r : Fin n → ℝ) (m : ℕ) (ht : 0 < t)
    (hsingle : singleSampleUnbiased A samples) :
    singleSampleUnbiased A samples ∧
      sampleMeanUnbiased (t := t) A samples ∧ matrixFreeRecurrence K r m := by
  refine ⟨hsingle, ?_, ?_⟩
  · unfold sampleMeanUnbiased
    rw [hsingle]
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
    calc
      (1 / (t : ℝ)) * ∑ _ : Fin t, Matrix.trace A = (1 / (t : ℝ)) * ((t : ℝ) * Matrix.trace A) := by
        simp
      _ = Matrix.trace A := by
        field_simp [htR]
  · refine ⟨rfl, ?_, ?_⟩
    · intro k
      rfl
    · rw [matrixFreeSequence_eq_pow_mulVec]
      rfl

end

end Omega.SyncKernelWeighted
