import Omega.Conclusion.BinfoldMellinTwoStepLaw
import Omega.Conclusion.BinfoldTwoConstantCompleteness
import Omega.Conclusion.BinfoldUniformOutputTwoatomChoquet
import Omega.Conclusion.FoldpiRanktwoFourMomentRigidity

namespace Omega.Conclusion

noncomputable section

/-- Paper-facing macro closure statement bundling the two-step Mellin law, the two-atom
Choquet limit, two-constant completeness, and rank-two four-moment rigidity. -/
def conclusion_binfold_twoatom_macro_closure_fourmoment_statement : Prop :=
  (∀ (q : ℝ) (_hq : 0 < q) (D : conclusion_binfold_mellin_two_step_law_data q),
      D.normalizedMomentLimit = D.phiInv + D.phiNegQMinusTwo) ∧
    (conclusion_binfold_uniform_output_twoatom_choquet_two_atom_law ∧
      conclusion_binfold_uniform_output_twoatom_choquet_capacity_closed_form ∧
      conclusion_binfold_uniform_output_twoatom_choquet_no_continuous_scale) ∧
    (∀ α φ c : ℝ, 1 < α → 1 < φ →
      twoAtomScalar α φ = twoAtomScalar α Real.goldenRatio → c = 2 * Real.pi →
        φ = Real.goldenRatio ∧ c = 2 * Real.pi ∧ BinfoldMellinEscortSemigroup φ) ∧
    (∀ (φ : ℝ) (f g : ℕ → ℝ),
      (∀ k, 1 ≤ k →
        f (k + 2) = (1 + φ ^ 2) * f (k + 1) - φ ^ 2 * f k) →
      (∃ A B : ℝ, ∀ k, 1 ≤ k → g (k + 2) = A * g (k + 1) + B * g k) →
      f 2 * f 2 - f 1 * f 3 ≠ 0 →
      g 1 = f 1 → g 2 = f 2 → g 3 = f 3 → g 4 = f 4 →
        ∀ k, 1 ≤ k → g k = f k)

/-- Paper label: `thm:conclusion-binfold-twoatom-macro-closure-fourmoment`. -/
theorem paper_conclusion_binfold_twoatom_macro_closure_fourmoment :
    conclusion_binfold_twoatom_macro_closure_fourmoment_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq D
    exact paper_conclusion_binfold_mellin_two_step_law q hq D
  · exact paper_conclusion_binfold_uniform_output_twoatom_choquet
  · intro α φ c hα hφ hScalar hCircle
    exact paper_conclusion_binfold_two_constant_completeness α φ c hα hφ hScalar hCircle
  · intro φ f g hrec_f hrec_g hdet h1 h2 h3 h4 k hk
    exact paper_conclusion_foldpi_ranktwo_four_moment_rigidity φ f g hrec_f hrec_g hdet
      h1 h2 h3 h4 k hk

end

end Omega.Conclusion
