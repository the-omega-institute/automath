import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-prefix package for the ZG Dirichlet truncations and their logarithmic
renormalization.  The Boolean `zeckendorfFinalDigit` records whether the final admissible
Zeckendorf digit contributes the new weight at the next truncation level. -/
structure xi_zg_dirichlet_log_renormalization_data where
  partialSum : ℕ → ℝ
  ratio : ℕ → ℝ
  zeckendorfWeight : ℕ → ℝ
  zeckendorfFinalDigit : ℕ → Bool
  renormalizedLog : ℕ → ℝ
  logMainTerm : ℕ → ℝ
  logErrorTerm : ℕ → ℝ
  renormalizedLimit : ℝ
  truncation_step_one :
    ∀ n, zeckendorfFinalDigit n = true →
      partialSum (n + 1) = partialSum n + zeckendorfWeight n
  truncation_step_zero :
    ∀ n, zeckendorfFinalDigit n = false →
      partialSum (n + 1) = partialSum n
  ratio_step_one :
    ∀ n, zeckendorfFinalDigit n = true →
      ratio (n + 1) = ratio n * (1 + zeckendorfWeight n / partialSum n)
  ratio_step_zero :
    ∀ n, zeckendorfFinalDigit n = false →
      ratio (n + 1) = ratio n
  renormalized_log_tends :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n, N ≤ n → |renormalizedLog n - renormalizedLimit| < ε
  log_factorization_eq :
    ∀ n, renormalizedLog n = logMainTerm n + logErrorTerm n

namespace xi_zg_dirichlet_log_renormalization_data

/-- The finite ZG truncation recurrence obtained by splitting on the final admissible digit. -/
def truncation_recurrence (D : xi_zg_dirichlet_log_renormalization_data) : Prop :=
  ∀ n,
    D.partialSum (n + 1) =
      D.partialSum n + if D.zeckendorfFinalDigit n then D.zeckendorfWeight n else 0

/-- The corresponding ratio recurrence after the same final-digit split. -/
def ratio_recurrence (D : xi_zg_dirichlet_log_renormalization_data) : Prop :=
  ∀ n,
    D.ratio (n + 1) =
      D.ratio n *
        (1 + if D.zeckendorfFinalDigit n then D.zeckendorfWeight n / D.partialSum n else 0)

/-- Epsilon form of convergence for the renormalized logarithmic correction series. -/
def renormalized_series_converges (D : xi_zg_dirichlet_log_renormalization_data) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n, N ≤ n → |D.renormalizedLog n - D.renormalizedLimit| < ε

/-- The renormalized logarithm factors into its explicit main term and convergent error term. -/
def log_factorization (D : xi_zg_dirichlet_log_renormalization_data) : Prop :=
  ∀ n, D.renormalizedLog n = D.logMainTerm n + D.logErrorTerm n

end xi_zg_dirichlet_log_renormalization_data

/-- Paper label: `thm:xi-zg-dirichlet-log-renormalization`. -/
theorem paper_xi_zg_dirichlet_log_renormalization
    (D : xi_zg_dirichlet_log_renormalization_data) :
    D.truncation_recurrence ∧ D.ratio_recurrence ∧ D.renormalized_series_converges ∧
      D.log_factorization := by
  refine ⟨?_, ?_, D.renormalized_log_tends, D.log_factorization_eq⟩
  · intro n
    cases hbit : D.zeckendorfFinalDigit n
    · simpa using D.truncation_step_zero n hbit
    · simpa using D.truncation_step_one n hbit
  · intro n
    cases hbit : D.zeckendorfFinalDigit n
    · simpa using D.ratio_step_zero n hbit
    · simpa using D.ratio_step_one n hbit

end Omega.Zeta
