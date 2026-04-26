import Mathlib.Tactic

namespace Omega.Zeta

/-- The finite source size of the Boolean fold layer `Ω_m = {0,1}^m`. -/
def xi_fold_profinite_haar_exponential_rate_omega_card (m : ℕ) : ℕ :=
  2 ^ m

/-- The finite-fiber mod-uniformity envelope after substituting `|Ω_m| = 2^m`. -/
noncomputable def xi_fold_profinite_haar_exponential_rate_tv_envelope
    (m q xCard : ℕ) : ℝ :=
  min 1 ((q : ℝ) * (xCard : ℝ) / (4 * (2 : ℝ) ^ m))

/-- A concrete exponential envelope used when `|X_m|` has Fibonacci growth. -/
noncomputable def xi_fold_profinite_haar_exponential_rate_fibonacci_envelope
    (C φ : ℝ) (m q : ℕ) : ℝ :=
  C * (q : ℝ) * (φ / 2) ^ m

/-- Finite quotient convergence to Haar, expressed through all fixed moduli. -/
def xi_fold_profinite_haar_exponential_rate_finite_quotient_converges
    (defect : ℕ → ℕ → ℝ) : Prop :=
  ∀ q ≥ 2, Filter.Tendsto (fun m => defect m q) Filter.atTop (nhds 0)

/-- Paper label: `cor:xi-fold-profinite-haar-exponential-rate`.

The finite-fiber mod-uniformity theorem gives the displayed total-variation envelope after the
fold substitution `|Ω_m| = 2^m`.  A Fibonacci count bound supplies the exponential envelope, and
finite quotient convergence packages the profinite Haar limit. -/
theorem paper_xi_fold_profinite_haar_exponential_rate
    (m q xCard : ℕ) (tvDefect jointDefect : ℝ)
    (defect : ℕ → ℕ → ℝ) (C φ : ℝ)
    (hTv :
      tvDefect ≤ xi_fold_profinite_haar_exponential_rate_tv_envelope m q xCard)
    (hJoint :
      jointDefect ≤ xi_fold_profinite_haar_exponential_rate_tv_envelope m q xCard)
    (hFib :
      xi_fold_profinite_haar_exponential_rate_tv_envelope m q xCard ≤
        xi_fold_profinite_haar_exponential_rate_fibonacci_envelope C φ m q)
    (hFiniteQuotients :
      xi_fold_profinite_haar_exponential_rate_finite_quotient_converges defect) :
    xi_fold_profinite_haar_exponential_rate_omega_card m = 2 ^ m ∧
      tvDefect ≤ xi_fold_profinite_haar_exponential_rate_tv_envelope m q xCard ∧
      jointDefect ≤ xi_fold_profinite_haar_exponential_rate_tv_envelope m q xCard ∧
      tvDefect ≤ xi_fold_profinite_haar_exponential_rate_fibonacci_envelope C φ m q ∧
      xi_fold_profinite_haar_exponential_rate_finite_quotient_converges defect := by
  refine ⟨rfl, hTv, hJoint, ?_, hFiniteQuotients⟩
  exact le_trans hTv hFib

end Omega.Zeta
