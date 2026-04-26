import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete sparse-audit parameters: the quality factor `Q` and boundary multiplier `delta`
are constrained only by the positive regime needed for the logarithmic decomposition. -/
abbrev xi_phi_sparse_toeplitz_audit_loglog_overhead_data :=
  { p : ℝ × ℝ //
    1 ≤ p.1 ∧ 1 ≤ Real.log (1 + p.2 * p.1) }

/-- The quality factor in the sparse Toeplitz audit threshold. -/
def xi_phi_sparse_toeplitz_audit_loglog_overhead_quality
    (D : xi_phi_sparse_toeplitz_audit_loglog_overhead_data) : ℝ :=
  D.1.1

/-- The boundary multiplier in the sparse Toeplitz audit threshold. -/
def xi_phi_sparse_toeplitz_audit_loglog_overhead_delta
    (D : xi_phi_sparse_toeplitz_audit_loglog_overhead_data) : ℝ :=
  D.1.2

/-- The iterated logarithmic factor `log (1 + delta * Q)`. -/
def xi_phi_sparse_toeplitz_audit_loglog_overhead_logFactor
    (D : xi_phi_sparse_toeplitz_audit_loglog_overhead_data) : ℝ :=
  Real.log
    (1 + xi_phi_sparse_toeplitz_audit_loglog_overhead_delta D *
      xi_phi_sparse_toeplitz_audit_loglog_overhead_quality D)

/-- Logarithm to the golden-ratio base. -/
def xi_phi_sparse_toeplitz_audit_loglog_overhead_logPhi (x : ℝ) : ℝ :=
  Real.log x / Real.log Real.goldenRatio

/-- The continuous threshold proxy for the first sparse audit index. -/
def xi_phi_sparse_toeplitz_audit_loglog_overhead_threshold
    (D : xi_phi_sparse_toeplitz_audit_loglog_overhead_data) : ℝ :=
  xi_phi_sparse_toeplitz_audit_loglog_overhead_quality D *
    xi_phi_sparse_toeplitz_audit_loglog_overhead_logFactor D

/-- The first ceiling index sufficient for the threshold proxy. -/
def xi_phi_sparse_toeplitz_audit_loglog_overhead_kStar
    (D : xi_phi_sparse_toeplitz_audit_loglog_overhead_data) : ℕ :=
  Nat.ceil
    (xi_phi_sparse_toeplitz_audit_loglog_overhead_logPhi
      (xi_phi_sparse_toeplitz_audit_loglog_overhead_threshold D)) + 1

/-- The paper's separated `log_phi Q + log_phi log(1 + delta Q)` ceiling bound. -/
def xi_phi_sparse_toeplitz_audit_loglog_overhead_bound
    (D : xi_phi_sparse_toeplitz_audit_loglog_overhead_data) : ℕ :=
  Nat.ceil
      (xi_phi_sparse_toeplitz_audit_loglog_overhead_logPhi
        (xi_phi_sparse_toeplitz_audit_loglog_overhead_quality D)) +
    Nat.ceil
      (xi_phi_sparse_toeplitz_audit_loglog_overhead_logPhi
        (xi_phi_sparse_toeplitz_audit_loglog_overhead_logFactor D)) + 2

/-- Concrete statement of the sparse Toeplitz audit logarithmic-overhead estimate. -/
def xi_phi_sparse_toeplitz_audit_loglog_overhead_statement
    (D : xi_phi_sparse_toeplitz_audit_loglog_overhead_data) : Prop :=
  xi_phi_sparse_toeplitz_audit_loglog_overhead_kStar D ≤
    xi_phi_sparse_toeplitz_audit_loglog_overhead_bound D

/-- Paper label: `thm:xi-phi-sparse-toeplitz-audit-loglog-overhead`. -/
theorem paper_xi_phi_sparse_toeplitz_audit_loglog_overhead
    (D : xi_phi_sparse_toeplitz_audit_loglog_overhead_data) :
    xi_phi_sparse_toeplitz_audit_loglog_overhead_statement D := by
  dsimp [xi_phi_sparse_toeplitz_audit_loglog_overhead_statement,
    xi_phi_sparse_toeplitz_audit_loglog_overhead_kStar,
    xi_phi_sparse_toeplitz_audit_loglog_overhead_bound,
    xi_phi_sparse_toeplitz_audit_loglog_overhead_threshold,
    xi_phi_sparse_toeplitz_audit_loglog_overhead_logPhi]
  let Q := xi_phi_sparse_toeplitz_audit_loglog_overhead_quality D
  let L := xi_phi_sparse_toeplitz_audit_loglog_overhead_logFactor D
  have hQ_ge : 1 ≤ Q := by
    simpa [Q, xi_phi_sparse_toeplitz_audit_loglog_overhead_quality] using D.2.1
  have hL_ge : 1 ≤ L := by
    simpa [L, xi_phi_sparse_toeplitz_audit_loglog_overhead_logFactor,
      xi_phi_sparse_toeplitz_audit_loglog_overhead_quality,
      xi_phi_sparse_toeplitz_audit_loglog_overhead_delta] using D.2.2
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ_ge
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_ge
  have hdecomp :
      Real.log (Q * L) / Real.log Real.goldenRatio =
        Real.log Q / Real.log Real.goldenRatio +
          Real.log L / Real.log Real.goldenRatio := by
    rw [Real.log_mul hQ_pos.ne' hL_pos.ne']
    ring
  have hceil :
      Nat.ceil (Real.log (Q * L) / Real.log Real.goldenRatio) ≤
        Nat.ceil (Real.log Q / Real.log Real.goldenRatio) +
          Nat.ceil (Real.log L / Real.log Real.goldenRatio) := by
    rw [hdecomp]
    exact Nat.ceil_add_le _ _
  have hmain :
      Nat.ceil
          (Real.log
            (xi_phi_sparse_toeplitz_audit_loglog_overhead_quality D *
              xi_phi_sparse_toeplitz_audit_loglog_overhead_logFactor D) /
            Real.log Real.goldenRatio) ≤
        Nat.ceil
            (Real.log (xi_phi_sparse_toeplitz_audit_loglog_overhead_quality D) /
              Real.log Real.goldenRatio) +
          Nat.ceil
            (Real.log (xi_phi_sparse_toeplitz_audit_loglog_overhead_logFactor D) /
              Real.log Real.goldenRatio) := by
    simpa [Q, L] using hceil
  omega

end

end Omega.Zeta
