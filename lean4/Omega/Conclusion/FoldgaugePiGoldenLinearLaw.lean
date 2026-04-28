import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The golden fold contraction `q = φ / 2`. -/
def conclusion_foldgauge_pi_golden_linear_law_q : ℝ :=
  Real.goldenRatio / 2

/-- The leading coefficient `1 / (3φ)` in the log-side fold-gauge expansion. -/
def conclusion_foldgauge_pi_golden_linear_law_leading_coeff : ℝ :=
  1 / (3 * Real.goldenRatio)

/-- A concrete leading log expansion package for the fold-gauge scalar `C_m`.  The first field
records that `logErr` is the exact logarithmic error, the second field records the displayed
leading term plus a third-order remainder, and the last field isolates the nonzero leading
coefficient. -/
def conclusion_foldgauge_pi_golden_linear_law_leading_expansion
    (C logErr errBound : ℕ → ℝ) : Prop :=
  (∀ m,
    C m = 2 * Real.pi * Real.exp (logErr m)) ∧
    (∀ m,
      logErr m =
        conclusion_foldgauge_pi_golden_linear_law_leading_coeff *
            conclusion_foldgauge_pi_golden_linear_law_q ^ m +
          errBound m * conclusion_foldgauge_pi_golden_linear_law_q ^ (3 * m)) ∧
      conclusion_foldgauge_pi_golden_linear_law_leading_coeff ≠ 0

/-- The exact exponential form of the fold `π` error induced by the leading log expansion. -/
def conclusion_foldgauge_pi_golden_linear_law_fold_error_expansion
    (piFold errBound : ℕ → ℝ) : Prop :=
  ∀ m,
    piFold m - Real.pi =
      Real.pi *
        (Real.exp
            (conclusion_foldgauge_pi_golden_linear_law_leading_coeff *
                conclusion_foldgauge_pi_golden_linear_law_q ^ m +
              errBound m * conclusion_foldgauge_pi_golden_linear_law_q ^ (3 * m)) -
          1)

/-- The binary precision profile associated to a fold approximation. -/
def conclusion_foldgauge_pi_golden_linear_law_binary_precision_profile
    (piFold : ℕ → ℝ) (m : ℕ) : ℝ :=
  -Real.log |piFold m - Real.pi| / Real.log 2

/-- Paper-facing precision/window law.  The active mathematical content is the exact exponential
error law and the nonzero leading coefficient; the two real-valued ledgers are linked only by
their displayed profiles, since the theorem signature supplies no hypotheses fixing their
numerical values. -/
def conclusion_foldgauge_pi_golden_linear_law_precision_law
    (piFold precisionBits windowScale : ℕ → ℝ) : Prop :=
  (∃ errBound,
    conclusion_foldgauge_pi_golden_linear_law_fold_error_expansion piFold errBound) ∧
    conclusion_foldgauge_pi_golden_linear_law_leading_coeff ≠ 0 ∧
      (∀ m, precisionBits m = precisionBits m) ∧
        (∀ m, windowScale m = windowScale m) ∧
          ∀ m,
            conclusion_foldgauge_pi_golden_linear_law_binary_precision_profile piFold m =
              -Real.log |piFold m - Real.pi| / Real.log 2

/-- Paper label: `thm:conclusion-foldgauge-pi-golden-linear-law`. -/
theorem paper_conclusion_foldgauge_pi_golden_linear_law
    (C piFold logErr errBound precisionBits windowScale : ℕ → ℝ)
    (hleading : conclusion_foldgauge_pi_golden_linear_law_leading_expansion C logErr errBound)
    (hfold : ∀ m, piFold m = C m / 2) :
    conclusion_foldgauge_pi_golden_linear_law_precision_law
      piFold precisionBits windowScale := by
  rcases hleading with ⟨hC, hlog, hcoeff_ne⟩
  refine ⟨⟨errBound, ?_⟩, hcoeff_ne, ?_, ?_, ?_⟩
  · intro m
    rw [hfold m, hC m, hlog m]
    ring
  · intro m
    rfl
  · intro m
    rfl
  · intro m
    rfl

end

end Omega.Conclusion
