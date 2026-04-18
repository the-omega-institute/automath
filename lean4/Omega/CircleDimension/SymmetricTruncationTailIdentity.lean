import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The symmetrized tail term `T(s) + T(1-s)` that models the Jacobi-theta tail integral appearing
in the symmetric truncation formulas. -/
noncomputable def symmetricTruncationTail (tail : ℂ → ℂ) (s : ℂ) : ℂ :=
  (tail s + tail (1 - s)) / 2

/-- The symmetric truncation of the completed zeta factor after subtracting the tail term. -/
noncomputable def symmetricTruncationLambda (LambdaZeta tail : ℂ → ℂ) (s : ℂ) : ℂ :=
  LambdaZeta s - symmetricTruncationTail tail s

/-- The completed `Ξ`-version of the symmetric truncation. -/
noncomputable def symmetricTruncationXi (LambdaZeta tail : ℂ → ℂ) (s : ℂ) : ℂ :=
  (s * (s - 1) / 2) * symmetricTruncationLambda LambdaZeta tail s

/-- The tail contribution after multiplying by the standard `Ξ` prefactor. -/
noncomputable def symmetricTruncationXiTail (tail : ℂ → ℂ) (s : ℂ) : ℂ :=
  (s * (s - 1) / 2) * symmetricTruncationTail tail s

lemma symmetricTruncationTail_self_dual
    (tail : ℂ → ℂ) (hTailDual : ∀ s, tail (1 - s) = tail s) (s : ℂ) :
    symmetricTruncationTail tail (1 - s) = symmetricTruncationTail tail s := by
  unfold symmetricTruncationTail
  have hs : (1 : ℂ) - (1 - s) = s := by ring
  rw [hTailDual s, hs]

/-- The symmetric truncation satisfies the exact tail decomposition by definition, and it inherits
the same `s ↔ 1-s` self-duality as the completed factor and the tail term.
    thm:cdim-symmetric-truncation-tail-identity -/
theorem paper_cdim_symmetric_truncation_tail_identity
    (LambdaZeta tail : ℂ → ℂ)
    (hLambdaDual : ∀ s, LambdaZeta (1 - s) = LambdaZeta s)
    (hTailDual : ∀ s, tail (1 - s) = tail s) :
    (∀ s, LambdaZeta s =
      symmetricTruncationLambda LambdaZeta tail s + symmetricTruncationTail tail s) ∧
      (∀ s, (s * (s - 1) / 2) * LambdaZeta s =
        symmetricTruncationXi LambdaZeta tail s + symmetricTruncationXiTail tail s) ∧
      (∀ s,
        symmetricTruncationLambda LambdaZeta tail (1 - s) =
          symmetricTruncationLambda LambdaZeta tail s) ∧
      (∀ s,
        symmetricTruncationXi LambdaZeta tail (1 - s) =
          symmetricTruncationXi LambdaZeta tail s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    unfold symmetricTruncationLambda
    ring
  · intro s
    unfold symmetricTruncationXi symmetricTruncationXiTail symmetricTruncationLambda
    ring
  · intro s
    unfold symmetricTruncationLambda
    rw [hLambdaDual, symmetricTruncationTail_self_dual tail hTailDual s]
  · intro s
    unfold symmetricTruncationXi
    have hpref :
        ((1 - s) * ((1 - s) - 1) / 2 : ℂ) = s * (s - 1) / 2 := by
      ring
    rw [hpref]
    have hLambda :
        symmetricTruncationLambda LambdaZeta tail (1 - s) =
          symmetricTruncationLambda LambdaZeta tail s := by
      unfold symmetricTruncationLambda
      rw [hLambdaDual, symmetricTruncationTail_self_dual tail hTailDual s]
    rw [hLambda]

end Omega.CircleDimension
