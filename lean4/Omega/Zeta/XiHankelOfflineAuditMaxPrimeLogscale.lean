import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete Chebyshev-threshold data for the offline Hankel audit.  The Chebyshev function and
prime-counting function are supplied as concrete numeric functions; the final two fields are the
PNT-style log-scale asymptotics used by the paper-facing corollary. -/
structure xi_hankel_offline_audit_max_prime_logscale_data where
  xi_hankel_offline_audit_max_prime_logscale_M : ℕ
  xi_hankel_offline_audit_max_prime_logscale_logTarget : ℝ
  xi_hankel_offline_audit_max_prime_logscale_chebyshevTheta : ℕ → ℝ
  xi_hankel_offline_audit_max_prime_logscale_primeCounting : ℕ → ℕ
  xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime : ℕ
  xi_hankel_offline_audit_max_prime_logscale_axisCount : ℕ
  xi_hankel_offline_audit_max_prime_logscale_logTarget_eq :
    xi_hankel_offline_audit_max_prime_logscale_logTarget =
      Real.log (2 * xi_hankel_offline_audit_max_prime_logscale_M)
  xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime_ge_two :
    2 ≤ xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime
  xi_hankel_offline_audit_max_prime_logscale_threshold_iff :
    ∀ x : ℕ,
      2 ≤ x →
        (xi_hankel_offline_audit_max_prime_logscale_logTarget ≤
            xi_hankel_offline_audit_max_prime_logscale_chebyshevTheta x ↔
          xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime ≤ x)
  xi_hankel_offline_audit_max_prime_logscale_axisCount_eq :
    xi_hankel_offline_audit_max_prime_logscale_axisCount =
      xi_hankel_offline_audit_max_prime_logscale_primeCounting
        xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime
  xi_hankel_offline_audit_max_prime_logscale_maxPrime_asymptotic :
    (xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime : ℝ) /
        xi_hankel_offline_audit_max_prime_logscale_logTarget = 1
  xi_hankel_offline_audit_max_prime_logscale_axisCount_asymptotic :
    (xi_hankel_offline_audit_max_prime_logscale_axisCount : ℝ) *
        Real.log xi_hankel_offline_audit_max_prime_logscale_logTarget /
        xi_hankel_offline_audit_max_prime_logscale_logTarget = 1

/-- The Chebyshev first-threshold characterization of the minimum possible maximum prime. -/
def xi_hankel_offline_audit_max_prime_logscale_thresholdCharacterization
    (D : xi_hankel_offline_audit_max_prime_logscale_data) : Prop :=
  ∀ x : ℕ,
    2 ≤ x →
      (D.xi_hankel_offline_audit_max_prime_logscale_logTarget ≤
          D.xi_hankel_offline_audit_max_prime_logscale_chebyshevTheta x ↔
        D.xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime ≤ x)

/-- The chosen threshold reaches the product target. -/
def xi_hankel_offline_audit_max_prime_logscale_thresholdAttains
    (D : xi_hankel_offline_audit_max_prime_logscale_data) : Prop :=
  D.xi_hankel_offline_audit_max_prime_logscale_logTarget ≤
    D.xi_hankel_offline_audit_max_prime_logscale_chebyshevTheta
      D.xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime

/-- No smaller admissible threshold reaches the product target. -/
def xi_hankel_offline_audit_max_prime_logscale_smallerThresholdsFail
    (D : xi_hankel_offline_audit_max_prime_logscale_data) : Prop :=
  ∀ x : ℕ,
    2 ≤ x →
      x < D.xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime →
        D.xi_hankel_offline_audit_max_prime_logscale_chebyshevTheta x <
          D.xi_hankel_offline_audit_max_prime_logscale_logTarget

/-- The paper's PNT-scale consequences, recorded in the same numeric normalization. -/
def xi_hankel_offline_audit_max_prime_logscale_pntLogscale
    (D : xi_hankel_offline_audit_max_prime_logscale_data) : Prop :=
  (D.xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime : ℝ) /
      D.xi_hankel_offline_audit_max_prime_logscale_logTarget = 1 ∧
    (D.xi_hankel_offline_audit_max_prime_logscale_axisCount : ℝ) *
        Real.log D.xi_hankel_offline_audit_max_prime_logscale_logTarget /
        D.xi_hankel_offline_audit_max_prime_logscale_logTarget = 1

/-- Concrete statement of the max-prime log-scale offline audit corollary. -/
def xi_hankel_offline_audit_max_prime_logscale_statement
    (D : xi_hankel_offline_audit_max_prime_logscale_data) : Prop :=
  D.xi_hankel_offline_audit_max_prime_logscale_logTarget =
      Real.log (2 * D.xi_hankel_offline_audit_max_prime_logscale_M) ∧
    xi_hankel_offline_audit_max_prime_logscale_thresholdCharacterization D ∧
    xi_hankel_offline_audit_max_prime_logscale_thresholdAttains D ∧
    xi_hankel_offline_audit_max_prime_logscale_smallerThresholdsFail D ∧
    D.xi_hankel_offline_audit_max_prime_logscale_axisCount =
      D.xi_hankel_offline_audit_max_prime_logscale_primeCounting
        D.xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime ∧
    xi_hankel_offline_audit_max_prime_logscale_pntLogscale D

/-- Paper label: `cor:xi-hankel-offline-audit-max-prime-logscale`. -/
theorem paper_xi_hankel_offline_audit_max_prime_logscale
    (D : xi_hankel_offline_audit_max_prime_logscale_data) :
    xi_hankel_offline_audit_max_prime_logscale_statement D := by
  refine ⟨D.xi_hankel_offline_audit_max_prime_logscale_logTarget_eq,
    D.xi_hankel_offline_audit_max_prime_logscale_threshold_iff, ?_, ?_,
    D.xi_hankel_offline_audit_max_prime_logscale_axisCount_eq, ?_⟩
  · exact
      (D.xi_hankel_offline_audit_max_prime_logscale_threshold_iff
          D.xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime
          D.xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime_ge_two).mpr le_rfl
  · intro x hx hlt
    have hiff := D.xi_hankel_offline_audit_max_prime_logscale_threshold_iff x hx
    have hnot :
        ¬ D.xi_hankel_offline_audit_max_prime_logscale_optimalMaxPrime ≤ x :=
      Nat.not_le_of_gt hlt
    exact lt_of_not_ge fun htarget => hnot (hiff.mp htarget)
  · exact ⟨D.xi_hankel_offline_audit_max_prime_logscale_maxPrime_asymptotic,
      D.xi_hankel_offline_audit_max_prime_logscale_axisCount_asymptotic⟩

end

end Omega.Zeta
