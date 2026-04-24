import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.FoldOutputEntropyGaugeAffineIdentity

namespace Omega.Conclusion

open FoldOutputEntropyGaugeAffineIdentityData

private theorem goldenRatio_sq_add_one_eq_mul_sqrt_five :
    1 + Real.goldenRatio ^ 2 = Real.goldenRatio * Real.sqrt 5 := by
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  rw [Real.goldenRatio]
  field_simp
  nlinarith

/-- Paper-facing constant rewrite for the fold-gauge entropy density: the affine identity and
gauge asymptotic are inherited from the existing entropy/gauge theorem, while the constant term is
rewritten using `1 + φ² = φ √5`.
    thm:conclusion-fold-gauge-entropy-density-exact-constant -/
theorem paper_conclusion_fold_gauge_entropy_density_exact_constant
    (D : Omega.Conclusion.FoldOutputEntropyGaugeAffineIdentityData) :
    D.kappaIdentity ∧
      D.gaugeDensityAsymptotic ∧
      1 + Real.goldenRatio ^ 2 = Real.goldenRatio * Real.sqrt 5 ∧
      (-Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2) =
        -Real.log Real.goldenRatio / (Real.goldenRatio * Real.sqrt 5)) := by
  rcases paper_conclusion_fold_output_entropy_gauge_affine_identity D with ⟨hkappa, hgauge⟩
  refine ⟨hkappa, hgauge, goldenRatio_sq_add_one_eq_mul_sqrt_five, ?_⟩
  rw [goldenRatio_sq_add_one_eq_mul_sqrt_five]

end Omega.Conclusion
