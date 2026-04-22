import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Renormalized finite-defect tail model after factoring off the nearest critical layer
`δ*`. The sign of `δ - δ*` dictates decay, bounded critical behavior, or blow-up. -/
noncomputable def finiteDefectCriticalTailModel (δ δStar : ℝ) (G E : ℝ → ℝ) : ℝ → ℝ :=
  fun ξ => Real.exp ((δ - δStar) * |ξ|) * G ξ + E ξ

/-- Concrete three-case package for the critical tail exponent: subcritical renormalizations
decay at rate `δ* - δ`, the critical renormalization differs from the leading trigonometric
polynomial by an exponentially small term, and any supercritical renormalization blows up along a
subsequence where the leading polynomial stays away from zero and the remainder is smaller than
half of the main term. -/
def finiteDefectCriticalTailExponentStatement : Prop :=
  ∀ {δStar g A c : ℝ} {G : ℝ → ℝ},
    0 < δStar →
      0 < g →
      0 ≤ A →
      0 < c →
      (∀ ξ, |G ξ| ≤ A) →
      (∀ δ : ℝ, δ < δStar →
        ∀ E : ℝ → ℝ,
          (∀ ξ, |E ξ| ≤ A * Real.exp (-(δStar - δ + g) * |ξ|)) →
          ∃ C > 0, ∀ ξ,
            |finiteDefectCriticalTailModel δ δStar G E ξ| ≤
              C * Real.exp (-(δStar - δ) * |ξ|)) ∧
      (∀ E : ℝ → ℝ,
        (∀ ξ, |E ξ| ≤ A * Real.exp (-g * |ξ|)) →
        ∀ ξ,
          |finiteDefectCriticalTailModel δStar δStar G E ξ - G ξ| ≤
            A * Real.exp (-g * |ξ|)) ∧
      (∀ δ : ℝ, δStar < δ →
        ∀ E : ℝ → ℝ,
          (∀ N : ℝ, 0 ≤ N →
            ∃ ξ, N ≤ |ξ| ∧ c ≤ |G ξ| ∧
              |E ξ| ≤ (c / 2) * Real.exp ((δ - δStar) * |ξ|)) →
          ∀ N : ℝ, 0 ≤ N →
            ∃ ξ, N ≤ |ξ| ∧
              (c / 2) * Real.exp ((δ - δStar) * |ξ|) ≤
                |finiteDefectCriticalTailModel δ δStar G E ξ|)

/-- Paper-facing wrapper for the finite-defect critical tail exponent package.
    thm:conclusion-finite-defect-critical-tail-exponent -/
def paper_conclusion_finite_defect_critical_tail_exponent : Prop :=
  finiteDefectCriticalTailExponentStatement

theorem paper_conclusion_finite_defect_critical_tail_exponent_proof :
    paper_conclusion_finite_defect_critical_tail_exponent := by
  intro δStar g A c G hδStar hg hA_nonneg hc hG
  refine ⟨?_, ?_, ?_⟩
  · intro δ hlt E hE
    refine ⟨2 * A + 1, by linarith, ?_⟩
    intro ξ
    have hExpNonneg : 0 ≤ Real.exp (-(δStar - δ) * |ξ|) := by positivity
    have hMain :
        |Real.exp ((δ - δStar) * |ξ|) * G ξ| ≤
          A * Real.exp (-(δStar - δ) * |ξ|) := by
      have hrewrite :
          Real.exp ((δ - δStar) * |ξ|) = Real.exp (-(δStar - δ) * |ξ|) := by
        congr 1
        ring
      rw [hrewrite, abs_mul, abs_of_nonneg hExpNonneg]
      calc
        Real.exp (-(δStar - δ) * |ξ|) * |G ξ| ≤
            Real.exp (-(δStar - δ) * |ξ|) * A := by
              gcongr
              exact hG ξ
        _ = A * Real.exp (-(δStar - δ) * |ξ|) := by ring
    have hFast :
        |E ξ| ≤ A * Real.exp (-(δStar - δ + g) * |ξ|) := hE ξ
    have hMonoExp :
        Real.exp (-(δStar - δ + g) * |ξ|) ≤
          Real.exp (-(δStar - δ) * |ξ|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg ξ, hg]
    have hRem :
        |E ξ| ≤ A * Real.exp (-(δStar - δ) * |ξ|) := by
      exact hFast.trans <| by
        gcongr
    have hTri :
        |finiteDefectCriticalTailModel δ δStar G E ξ| ≤
          |Real.exp ((δ - δStar) * |ξ|) * G ξ| + |E ξ| := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · dsimp [finiteDefectCriticalTailModel]
        nlinarith [neg_abs_le (Real.exp ((δ - δStar) * |ξ|) * G ξ), neg_abs_le (E ξ)]
      · dsimp [finiteDefectCriticalTailModel]
        nlinarith [le_abs_self (Real.exp ((δ - δStar) * |ξ|) * G ξ), le_abs_self (E ξ)]
    have hTwoA :
        |finiteDefectCriticalTailModel δ δStar G E ξ| ≤
          (2 * A) * Real.exp (-(δStar - δ) * |ξ|) := by
      nlinarith
    have hLift :
        (2 * A) * Real.exp (-(δStar - δ) * |ξ|) ≤
          (2 * A + 1) * Real.exp (-(δStar - δ) * |ξ|) := by
      nlinarith [Real.exp_pos (-(δStar - δ) * |ξ|)]
    exact hTwoA.trans hLift
  · intro E hE ξ
    simpa [finiteDefectCriticalTailModel] using hE ξ
  · intro δ hgt E hwit N hN
    rcases hwit N hN with ⟨ξ, hξN, hGξ, hEξ⟩
    refine ⟨ξ, hξN, ?_⟩
    have hExpNonneg : 0 ≤ Real.exp ((δ - δStar) * |ξ|) := by positivity
    have hScaled :
        c * Real.exp ((δ - δStar) * |ξ|) ≤
          |Real.exp ((δ - δStar) * |ξ|) * G ξ| := by
      rw [abs_mul, abs_of_nonneg hExpNonneg]
      calc
        c * Real.exp ((δ - δStar) * |ξ|) ≤ |G ξ| * Real.exp ((δ - δStar) * |ξ|) := by
          gcongr
        _ = Real.exp ((δ - δStar) * |ξ|) * |G ξ| := by ring
    have hRev :
        |Real.exp ((δ - δStar) * |ξ|) * G ξ| ≤
          |finiteDefectCriticalTailModel δ δStar G E ξ| + |E ξ| := by
      have hAux :
          |finiteDefectCriticalTailModel δ δStar G E ξ + (-E ξ)| ≤
            |finiteDefectCriticalTailModel δ δStar G E ξ| + |-E ξ| := by
        refine abs_le.mpr ⟨?_, ?_⟩
        · nlinarith [neg_abs_le (finiteDefectCriticalTailModel δ δStar G E ξ), neg_abs_le (-E ξ)]
        · nlinarith [le_abs_self (finiteDefectCriticalTailModel δ δStar G E ξ), le_abs_self (-E ξ)]
      simpa [finiteDefectCriticalTailModel, add_comm, add_left_comm, add_assoc, abs_neg] using hAux
    nlinarith

end Omega.Conclusion
