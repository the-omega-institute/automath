import Mathlib

namespace Omega.Discussion

/-- The Fourier multiplier of the Poisson kernel on `ℝ`. -/
noncomputable def poissonFourierMultiplier (t ξ : ℝ) : ℝ :=
  Real.exp (-t * |ξ|)

/-- The Dirichlet-to-Neumann generator symbol on `ℝ`. -/
noncomputable def dtnGeneratorSymbol (ξ : ℝ) : ℝ :=
  |ξ|

/-- The boundary normal derivative acts by the negative DtN symbol. -/
noncomputable def boundaryNormalDerivativeSymbol (ξ : ℝ) : ℝ :=
  -dtnGeneratorSymbol ξ

lemma hasDerivAt_poissonFourierMultiplier (ξ t : ℝ) :
    HasDerivAt (fun y => poissonFourierMultiplier y ξ)
      (boundaryNormalDerivativeSymbol ξ * poissonFourierMultiplier t ξ) t := by
  have hlin : HasDerivAt (fun y : ℝ => -y * |ξ|) (-|ξ|) t := by
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id t).neg).mul_const |ξ|)
  simpa [poissonFourierMultiplier, boundaryNormalDerivativeSymbol, dtnGeneratorSymbol,
    mul_comm, mul_left_comm, mul_assoc] using hlin.exp

lemma normalized_even_homogeneous_eq_abs {ψ : ℝ → ℝ}
    (heven : ∀ x, ψ (-x) = ψ x)
    (hhom : ∀ a x, 0 ≤ a → ψ (a * x) = a * ψ x)
    (hnorm : ψ 1 = 1) :
    ∀ ξ, ψ ξ = |ξ| := by
  intro ξ
  by_cases hξ : 0 ≤ ξ
  · calc
      ψ ξ = ψ (ξ * 1) := by simp
      _ = ξ * ψ 1 := by simpa using hhom ξ 1 hξ
      _ = |ξ| := by simp [hnorm, abs_of_nonneg hξ]
  · have hneg : 0 ≤ -ξ := by linarith
    have hlt : ξ < 0 := lt_of_not_ge hξ
    calc
      ψ ξ = ψ (-ξ) := by simpa using (heven ξ).symm
      _ = (-ξ) * ψ 1 := by simpa using hhom (-ξ) 1 hneg
      _ = |ξ| := by simp [hnorm, abs_of_neg hlt]

/-- Paper-facing DtN generator package: the Poisson kernel has Fourier multiplier `e^{-t |ξ|}`,
the boundary normal derivative is `-|D|`, and a normalized even one-homogeneous translation-
invariant symbol on `ℝ` must equal `|ξ|`.
    prop:discussion-dtn-generator -/
theorem paper_discussion_dtn_generator (t ξ : ℝ) :
    poissonFourierMultiplier t ξ = Real.exp (t * boundaryNormalDerivativeSymbol ξ) ∧
      HasDerivAt (fun y => poissonFourierMultiplier y ξ)
        (boundaryNormalDerivativeSymbol ξ * poissonFourierMultiplier t ξ) t ∧
      (∀ ψ : ℝ → ℝ,
        (∀ x, ψ (-x) = ψ x) →
          (∀ a x, 0 ≤ a → ψ (a * x) = a * ψ x) →
            ψ 1 = 1 → ψ ξ = dtnGeneratorSymbol ξ) := by
  refine ⟨?_, hasDerivAt_poissonFourierMultiplier ξ t, ?_⟩
  · simp [poissonFourierMultiplier, boundaryNormalDerivativeSymbol, dtnGeneratorSymbol,
      mul_comm]
  · intro ψ heven hhom hnorm
    simpa [dtnGeneratorSymbol] using normalized_even_homogeneous_eq_abs heven hhom hnorm ξ

end Omega.Discussion
