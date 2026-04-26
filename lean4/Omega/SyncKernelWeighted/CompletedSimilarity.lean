import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.SyncKernelWeighted.SelfDualNormalForm1pmu

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Fixed audited seed used for the completed-similarity normalization. -/
def completed_similarity_seed : SelfDualBlockMatrix :=
  { X := 1, Y := 2, Z := 3, W := 4 }

/-- The completed matrix `\widetilde B(θ) = exp(-θ / 2) • B(exp θ)` in the concrete block model. -/
def completed_similarity_completed (θ : ℂ) : SelfDualBlockMatrix :=
  let B := selfDualFamily (Complex.exp θ) completed_similarity_seed
  { X := Complex.exp (-θ / 2) * B.X
    Y := Complex.exp (-θ / 2) * B.Y
    Z := Complex.exp (-θ / 2) * B.Z
    W := Complex.exp (-θ / 2) * B.W }

/-- Quadratic characteristic polynomial of the completed `2 × 2` block matrix. -/
def completed_similarity_charpoly (θ x : ℂ) : ℂ :=
  let B := completed_similarity_completed θ
  (x - B.X) * (x - B.W) - B.Y * B.Z

/-- Paper label: `lem:completed-similarity`. After the completion factor `exp(-θ / 2)`, the
self-duality involution sends `θ` to `-θ`; because the involution only flips the off-diagonal
entries, the quadratic characteristic polynomial is even in `θ`. -/
theorem paper_completed_similarity (θ : ℂ) :
    selfDualPiConj (completed_similarity_completed θ) = completed_similarity_completed (-θ) ∧
      ∀ x : ℂ, completed_similarity_charpoly θ x = completed_similarity_charpoly (-θ) x := by
  have hexp_half :
      Complex.exp (-θ / 2) * Complex.exp θ = Complex.exp (θ / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hexp_neg_half :
      Complex.exp (θ / 2) * Complex.exp (-θ) = Complex.exp (-θ / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hexp_half_mul (a : ℂ) :
      Complex.exp (-θ / 2) * (Complex.exp θ * a) = Complex.exp (θ / 2) * a := by
    calc
      Complex.exp (-θ / 2) * (Complex.exp θ * a) =
          (Complex.exp (-θ / 2) * Complex.exp θ) * a := by ring
      _ = Complex.exp (θ / 2) * a := by rw [hexp_half]
  have hexp_neg_half_mul (a : ℂ) :
      Complex.exp (θ / 2) * (Complex.exp (-θ) * a) = Complex.exp (-θ / 2) * a := by
    calc
      Complex.exp (θ / 2) * (Complex.exp (-θ) * a) =
          (Complex.exp (θ / 2) * Complex.exp (-θ)) * a := by ring
      _ = Complex.exp (-θ / 2) * a := by rw [hexp_neg_half]
  have hcompleted :
      selfDualPiConj (completed_similarity_completed θ) = completed_similarity_completed (-θ) := by
    ext
    · simp [completed_similarity_completed, completed_similarity_seed, selfDualPiConj,
        selfDualFamily, mul_add, hexp_half, hexp_neg_half]
      ring_nf
    · simp [completed_similarity_completed, completed_similarity_seed, selfDualPiConj,
        selfDualFamily, mul_add]
      rw [hexp_half_mul, hexp_neg_half_mul]
    · simp [completed_similarity_completed, completed_similarity_seed, selfDualPiConj,
        selfDualFamily, mul_add]
      rw [hexp_half_mul, hexp_neg_half_mul]
    · simp [completed_similarity_completed, completed_similarity_seed, selfDualPiConj,
        selfDualFamily, mul_add]
      rw [hexp_half_mul, hexp_neg_half_mul]
      ring_nf
  refine ⟨hcompleted, ?_⟩
  intro x
  have hX :
      (completed_similarity_completed θ).X = (completed_similarity_completed (-θ)).X := by
    simpa [selfDualPiConj] using congrArg SelfDualBlockMatrix.X hcompleted
  have hY :
      (completed_similarity_completed (-θ)).Y = -(completed_similarity_completed θ).Y := by
    simpa [selfDualPiConj] using (congrArg SelfDualBlockMatrix.Y hcompleted).symm
  have hZ :
      (completed_similarity_completed (-θ)).Z = -(completed_similarity_completed θ).Z := by
    simpa [selfDualPiConj] using (congrArg SelfDualBlockMatrix.Z hcompleted).symm
  have hW :
      (completed_similarity_completed θ).W = (completed_similarity_completed (-θ)).W := by
    simpa [selfDualPiConj] using congrArg SelfDualBlockMatrix.W hcompleted
  dsimp [completed_similarity_charpoly]
  rw [hX, hW, hY, hZ]
  ring

end

end Omega.SyncKernelWeighted
