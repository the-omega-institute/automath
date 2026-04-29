import Omega.Conclusion.LinearExternalizationLiminf

namespace Omega.Conclusion

open Filter

/-- A conclusion-level rewrite strategy records the rewrite lower-tail data needed by the existing
linear-externalization theorem together with the prime-register residual-support identification. -/
structure cor_conclusion_prime_register_residual_support_linear_incompressibility_ConclusionRewriteStrategy where
  rewriteTailProb : ℚ → ℕ → ℝ
  gaugeTailProb : ℚ → ℕ → ℝ
  eventuallyAbove : ℚ → Prop
  rewrite_le_gauge : ∀ q m, rewriteTailProb q m ≤ gaugeTailProb q m
  gaugeExponential :
    ∀ q : ℚ, (q : ℝ) < 4 / 27 →
      ∃ c > 0, ∀ᶠ m in atTop, gaugeTailProb q m ≤ Real.exp (-c * m)
  summable_of_exponential :
    ∀ q : ℚ,
      (∃ c > 0, ∀ᶠ m in atTop, rewriteTailProb q m ≤ Real.exp (-c * m)) →
        Summable (rewriteTailProb q)
  borelCantelli : ∀ q : ℚ, Summable (rewriteTailProb q) → eventuallyAbove q
  residualSupportTailProb : ℚ → ℕ → ℝ
  residualSupportEventuallyAbove : ℚ → Prop
  residualTail_eq_rewrite : ∀ q m, residualSupportTailProb q m = rewriteTailProb q m
  residualAbove_iff : ∀ q, residualSupportEventuallyAbove q ↔ eventuallyAbove q

/-- The residual-support form of the `R = 3` linear externalization theorem: every rational
threshold below `4 / 27` is eventually violated almost surely, and the corresponding lower tail is
exponentially small. -/
def cor_conclusion_prime_register_residual_support_linear_incompressibility_ConclusionPrimeRegisterResidualSupportLinearIncompressibility
    (S :
      cor_conclusion_prime_register_residual_support_linear_incompressibility_ConclusionRewriteStrategy) :
    Prop :=
  (∀ q : ℚ, (q : ℝ) < 4 / 27 → S.residualSupportEventuallyAbove q) ∧
    ∀ q : ℚ, (q : ℝ) < 4 / 27 →
      ∃ c > 0, ∀ᶠ m in atTop, S.residualSupportTailProb q m ≤ Real.exp (-c * m)

local notation "ConclusionRewriteStrategy" =>
  cor_conclusion_prime_register_residual_support_linear_incompressibility_ConclusionRewriteStrategy

local notation "ConclusionPrimeRegisterResidualSupportLinearIncompressibility" =>
  cor_conclusion_prime_register_residual_support_linear_incompressibility_ConclusionPrimeRegisterResidualSupportLinearIncompressibility

/-- Paper label: `cor:conclusion-prime-register-residual-support-linear-incompressibility`. -/
theorem paper_conclusion_prime_register_residual_support_linear_incompressibility
    (S : ConclusionRewriteStrategy) :
    ConclusionPrimeRegisterResidualSupportLinearIncompressibility S := by
  let D : LinearExternalizationLiminfData := {
    R := 3
    rewriteTailProb := S.rewriteTailProb
    gaugeTailProb := S.gaugeTailProb
    eventuallyAbove := S.eventuallyAbove
    hR := by norm_num
    rewrite_le_gauge := S.rewrite_le_gauge
    gaugeExponential := by
      intro q hq
      have hq' : (q : ℝ) < 4 / 27 := by
        norm_num at hq ⊢
        exact hq
      exact S.gaugeExponential q hq'
    summable_of_exponential := S.summable_of_exponential
    borelCantelli := S.borelCantelli
  }
  have hmain := paper_conclusion_linear_externalization_liminf D
  refine ⟨?_, ?_⟩
  · intro q hq
    have hq' : (q : ℝ) < 4 / (9 * D.R) := by
      change (q : ℝ) < 4 / (9 * (3 : ℝ))
      norm_num
      exact hq
    exact (S.residualAbove_iff q).2 (hmain.1 q hq')
  · intro q hq
    have hq' : (q : ℝ) < 4 / (9 * D.R) := by
      change (q : ℝ) < 4 / (9 * (3 : ℝ))
      norm_num
      exact hq
    rcases hmain.2 q hq' with ⟨c, hc, htail⟩
    refine ⟨c, hc, ?_⟩
    filter_upwards [htail] with m hm
    simpa [S.residualTail_eq_rewrite q m] using hm

end Omega.Conclusion
