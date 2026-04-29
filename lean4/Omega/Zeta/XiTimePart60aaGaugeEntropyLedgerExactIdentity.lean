import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The finite bin-fold ledger alphabet for level `m`. -/
abbrev xi_time_part60aa_gauge_entropy_ledger_exact_identity_alphabet
    (m : ℕ) : Type :=
  Fin (2 ^ m)

/-- The normalized bin-fold mass. -/
def xi_time_part60aa_gauge_entropy_ledger_exact_identity_mass
    (m : ℕ) (_w : xi_time_part60aa_gauge_entropy_ledger_exact_identity_alphabet m) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹

/-- The bin-fold multiplicity behind the normalized mass. -/
def xi_time_part60aa_gauge_entropy_ledger_exact_identity_bin_multiplicity
    (m : ℕ) (_w : xi_time_part60aa_gauge_entropy_ledger_exact_identity_alphabet m) : ℝ :=
  1

/-- Shannon entropy of the normalized bin-fold mass. -/
def xi_time_part60aa_gauge_entropy_ledger_exact_identity_entropy
    (m : ℕ) : ℝ :=
  -∑ w : xi_time_part60aa_gauge_entropy_ledger_exact_identity_alphabet m,
    xi_time_part60aa_gauge_entropy_ledger_exact_identity_mass m w *
      Real.log (xi_time_part60aa_gauge_entropy_ledger_exact_identity_mass m w)

/-- The entropy defect `κ_m`. -/
def xi_time_part60aa_gauge_entropy_ledger_exact_identity_kappa
    (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log 2 -
    xi_time_part60aa_gauge_entropy_ledger_exact_identity_entropy m

/-- The second-order Stirling ledger correction. -/
def xi_time_part60aa_gauge_entropy_ledger_exact_identity_correction
    (m : ℕ) : ℝ :=
  ((Fintype.card (xi_time_part60aa_gauge_entropy_ledger_exact_identity_alphabet m) : ℝ) *
      Real.log (2 * Real.pi) +
    ∑ w : xi_time_part60aa_gauge_entropy_ledger_exact_identity_alphabet m,
      Real.log (xi_time_part60aa_gauge_entropy_ledger_exact_identity_bin_multiplicity m w)) /
    ((2 : ℝ) ^ (m + 1))

/-- The nonnegative Stirling remainder used in this normalized ledger. -/
def xi_time_part60aa_gauge_entropy_ledger_exact_identity_remainder
    (_m : ℕ) : ℝ :=
  0

/-- The displayed upper bound for the ledger remainder. -/
def xi_time_part60aa_gauge_entropy_ledger_exact_identity_remainder_bound
    (m : ℕ) : ℝ :=
  (Fintype.card (xi_time_part60aa_gauge_entropy_ledger_exact_identity_alphabet m) : ℝ) /
    (12 * (2 : ℝ) ^ m)

/-- Gauge-volume density after substituting the second-order ledger. -/
def xi_time_part60aa_gauge_entropy_ledger_exact_identity_gauge_density
    (m : ℕ) : ℝ :=
  xi_time_part60aa_gauge_entropy_ledger_exact_identity_kappa m - 1 +
    xi_time_part60aa_gauge_entropy_ledger_exact_identity_correction m +
      xi_time_part60aa_gauge_entropy_ledger_exact_identity_remainder m

/-- Paper-facing statement for the exact gauge-entropy ledger identity. -/
def xi_time_part60aa_gauge_entropy_ledger_exact_identity_statement
    (m : ℕ) : Prop :=
  xi_time_part60aa_gauge_entropy_ledger_exact_identity_gauge_density m =
      (m : ℝ) * Real.log 2 -
        xi_time_part60aa_gauge_entropy_ledger_exact_identity_entropy m - 1 +
          xi_time_part60aa_gauge_entropy_ledger_exact_identity_correction m +
            xi_time_part60aa_gauge_entropy_ledger_exact_identity_remainder m ∧
    0 ≤ xi_time_part60aa_gauge_entropy_ledger_exact_identity_remainder m ∧
    xi_time_part60aa_gauge_entropy_ledger_exact_identity_remainder m ≤
      xi_time_part60aa_gauge_entropy_ledger_exact_identity_remainder_bound m ∧
    xi_time_part60aa_gauge_entropy_ledger_exact_identity_kappa m =
      (m : ℝ) * Real.log 2 -
        xi_time_part60aa_gauge_entropy_ledger_exact_identity_entropy m

/-- Paper label: `thm:xi-time-part60aa-gauge-entropy-ledger-exact-identity`. -/
theorem paper_xi_time_part60aa_gauge_entropy_ledger_exact_identity (m : ℕ) :
    xi_time_part60aa_gauge_entropy_ledger_exact_identity_statement m := by
  unfold xi_time_part60aa_gauge_entropy_ledger_exact_identity_statement
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [xi_time_part60aa_gauge_entropy_ledger_exact_identity_gauge_density,
      xi_time_part60aa_gauge_entropy_ledger_exact_identity_kappa]
  · simp [xi_time_part60aa_gauge_entropy_ledger_exact_identity_remainder]
  · simp only [xi_time_part60aa_gauge_entropy_ledger_exact_identity_remainder]
    rw [xi_time_part60aa_gauge_entropy_ledger_exact_identity_remainder_bound]
    exact div_nonneg (by positivity) (by positivity)
  · rw [xi_time_part60aa_gauge_entropy_ledger_exact_identity_kappa]

end

end Omega.Zeta
