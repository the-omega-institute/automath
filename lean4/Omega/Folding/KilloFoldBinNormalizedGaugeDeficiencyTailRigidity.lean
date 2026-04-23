import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Omega.Folding.FoldBinGaugeBernoulliExtractionOperator
import Omega.Folding.KilloFoldBinNormalizedGaugeDeficiency

namespace Omega.Folding

noncomputable section

/-- Exponentiating the tail values produces a normalization constant whose logarithm recovers the
original normalized gauge-deficiency sequence. -/
def killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_normalization
    (Δ : ℕ → ℚ) : ℕ → ℝ :=
  fun m => Real.exp (Δ m)

/-- The tail-extraction datum obtained by reindexing a tail from `m₀` onward. -/
def killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extraction_data
    (Δ : ℕ → ℚ) (m₀ : ℕ) : FoldBinGaugeBernoulliExtractionData where
  targetCoeff r := Δ (m₀ + r)

/-- Bernoulli coefficients recovered from the reindexed tail. -/
def killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extracted_coeff
    (Δ : ℕ → ℚ) (m₀ r : ℕ) : ℚ :=
  (killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extraction_data Δ m₀).extractedCoeff r

/-- The even-zeta value recovered from the extracted coefficient by the standard Bernoulli--zeta
formula. -/
def killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_recovered_zeta
    (Δ : ℕ → ℚ) (m₀ r : ℕ) : ℝ :=
  (-1 : ℝ) ^ (r + 1) * (2 : ℝ) ^ (2 * r - 1) * Real.pi ^ (2 * r) *
    (killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extracted_coeff Δ m₀ r : ℝ) /
      (Nat.factorial (2 * r) : ℝ)

/-- Paper label: `cor:killo-fold-bin-normalized-gauge-deficiency-tail-rigidity`.  Eventual
agreement of two normalized gauge-deficiency tails forces agreement of the reindexed extracted
Bernoulli coefficients and therefore of the recovered even-zeta values. -/
theorem paper_killo_fold_bin_normalized_gauge_deficiency_tail_rigidity
    (Δ₁ Δ₂ : ℕ → ℚ) (m₀ r : ℕ) (hr : 1 ≤ r)
    (htail : ∀ m, m₀ ≤ m → Δ₁ m = Δ₂ m) :
    (∀ m, m₀ ≤ m →
      killoFoldBinNormalizedGaugeDeficiency
          (killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_normalization Δ₁) m =
        killoFoldBinNormalizedGaugeDeficiency
          (killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_normalization Δ₂) m) ∧
      killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extracted_coeff Δ₁ m₀ r =
        killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extracted_coeff Δ₂ m₀ r ∧
      killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_recovered_zeta Δ₁ m₀ r =
        killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_recovered_zeta Δ₂ m₀ r := by
  have hcoeff1 :=
    paper_fold_bin_gauge_bernoulli_extraction_operator
      (killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extraction_data Δ₁ m₀) r hr
  have hcoeff2 :=
    paper_fold_bin_gauge_bernoulli_extraction_operator
      (killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extraction_data Δ₂ m₀) r hr
  have htailr : Δ₁ (m₀ + r) = Δ₂ (m₀ + r) := by
    exact htail (m₀ + r) (Nat.le_add_right m₀ r)
  have hextracted :
      killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extracted_coeff Δ₁ m₀ r =
        killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extracted_coeff Δ₂ m₀ r := by
    calc
      killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extracted_coeff Δ₁ m₀ r
          = Δ₁ (m₀ + r) := by
              simpa [killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extracted_coeff,
                killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extraction_data] using
                hcoeff1
      _ = Δ₂ (m₀ + r) := htailr
      _ = killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extracted_coeff Δ₂ m₀ r := by
            simpa [killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extracted_coeff,
              killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_extraction_data] using
              hcoeff2.symm
  refine ⟨?_, hextracted, ?_⟩
  · intro m hm
    simp [killoFoldBinNormalizedGaugeDeficiency,
      killoFoldBinNormalizationConstant,
      killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_normalization, htail m hm]
  · simp [killo_fold_bin_normalized_gauge_deficiency_tail_rigidity_recovered_zeta, hextracted]

end

end Omega.Folding
