import Omega.POM.GoldenLikelihoodRatioMartingales

namespace Omega.POM

lemma pom_golden_esscher_symmetrization_plusProb_eq_rpow_neg_one :
    pom_golden_likelihood_ratio_martingales_plusProb =
      Real.goldenRatio ^ (-(1 : ℝ)) := by
  rw [pom_golden_likelihood_ratio_martingales_plusProb, Real.rpow_neg_one]

lemma pom_golden_esscher_symmetrization_minusProb_eq_rpow_neg_two :
    pom_golden_likelihood_ratio_martingales_minusProb =
      Real.goldenRatio ^ (-(2 : ℝ)) := by
  have hφ : 0 < Real.goldenRatio := Real.goldenRatio_pos
  calc
    pom_golden_likelihood_ratio_martingales_minusProb
        = (Real.goldenRatio ^ (-(1 : ℝ))) ^ 2 := by
          rw [pom_golden_likelihood_ratio_martingales_minusProb,
            pom_golden_esscher_symmetrization_plusProb_eq_rpow_neg_one]
    _ = Real.goldenRatio ^ (-(1 : ℝ)) * Real.goldenRatio ^ (-(1 : ℝ)) := by ring
    _ = Real.goldenRatio ^ (-(1 : ℝ) + -(1 : ℝ)) := by rw [Real.rpow_add hφ]
    _ = Real.goldenRatio ^ (-(2 : ℝ)) := by norm_num

/-- Paper label: `prop:pom-golden-esscher-symmetrization`. The Esscher half-tilt normalizer
balances the two complementary golden one-step masses to equal probability. -/
theorem paper_pom_golden_esscher_symmetrization :
    let normalizer : Real := 2 * Real.goldenRatio ^ (-(3 : Real) / 2)
    (pom_golden_likelihood_ratio_martingales_plusProb *
          Real.goldenRatio ^ (-(1 : Real) / 2)) / normalizer = (1 : Real) / 2 ∧
      (pom_golden_likelihood_ratio_martingales_minusProb *
          Real.goldenRatio ^ ((1 : Real) / 2)) / normalizer = (1 : Real) / 2 := by
  have hφ : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hpow_ne : Real.goldenRatio ^ (-(3 : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hφ _)
  have hplus :
      pom_golden_likelihood_ratio_martingales_plusProb *
          Real.goldenRatio ^ (-(1 : ℝ) / 2) =
        Real.goldenRatio ^ (-(3 : ℝ) / 2) := by
    calc
      pom_golden_likelihood_ratio_martingales_plusProb *
          Real.goldenRatio ^ (-(1 : ℝ) / 2)
          = Real.goldenRatio ^ (-(1 : ℝ)) *
              Real.goldenRatio ^ (-(1 : ℝ) / 2) := by
                rw [pom_golden_esscher_symmetrization_plusProb_eq_rpow_neg_one]
      _ = Real.goldenRatio ^ (-(1 : ℝ) + -(1 : ℝ) / 2) := by rw [Real.rpow_add hφ]
      _ = Real.goldenRatio ^ (-(3 : ℝ) / 2) := by norm_num
  have hminus :
      pom_golden_likelihood_ratio_martingales_minusProb *
          Real.goldenRatio ^ ((1 : ℝ) / 2) =
        Real.goldenRatio ^ (-(3 : ℝ) / 2) := by
    calc
      pom_golden_likelihood_ratio_martingales_minusProb *
          Real.goldenRatio ^ ((1 : ℝ) / 2)
          = Real.goldenRatio ^ (-(2 : ℝ)) * Real.goldenRatio ^ ((1 : ℝ) / 2) := by
                rw [pom_golden_esscher_symmetrization_minusProb_eq_rpow_neg_two]
      _ = Real.goldenRatio ^ (-(2 : ℝ) + (1 : ℝ) / 2) := by rw [Real.rpow_add hφ]
      _ = Real.goldenRatio ^ (-(3 : ℝ) / 2) := by norm_num
  dsimp
  constructor
  · rw [hplus]
    field_simp [hpow_ne]
  · rw [hminus]
    field_simp [hpow_ne]

end Omega.POM
