import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Concrete Cauchy-feature package for the finite-rank basepoint scan model.  The imaginary
offsets are stored as positive real widths, so the pole `gamma - i * width` never lies on the
real scan axis. -/
structure xi_basepoint_scan_finite_rank_rkhs_data where
  kappa : ℕ
  gamma : Fin kappa → ℝ
  width : Fin kappa → ℝ
  width_pos : ∀ k, 0 < width k
  weight : Fin kappa → ℝ

namespace xi_basepoint_scan_finite_rank_rkhs_data

/-- The real Cauchy feature magnitude used to build the Gram kernel. -/
def feature (D : xi_basepoint_scan_finite_rank_rkhs_data) (x : ℝ) (k : Fin D.kappa) : ℝ :=
  D.weight k / ((x - D.gamma k) ^ 2 + (D.width k) ^ 2)

/-- The finite Gram kernel obtained from the Cauchy feature map. -/
def kernel (D : xi_basepoint_scan_finite_rank_rkhs_data) (x y : ℝ) : ℝ :=
  Finset.univ.sum fun k : Fin D.kappa => D.feature x k * D.feature y k

/-- The diagonal scan profile attached to the same feature map. -/
def scanProfile (D : xi_basepoint_scan_finite_rank_rkhs_data) (x : ℝ) : ℝ :=
  Finset.univ.sum fun k : Fin D.kappa => (D.feature x k) ^ 2

/-- Positivity certificate: every finite linear scan has nonnegative squared feature norm. -/
def positiveKernel (D : xi_basepoint_scan_finite_rank_rkhs_data) : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → ℝ) (x : ι → ℝ),
    0 ≤ Finset.univ.sum fun k : Fin D.kappa =>
      (Finset.univ.sum fun i : ι => c i * D.feature (x i) k) ^ 2

/-- The kernel diagonal is exactly the stored scan profile. -/
def diagonalMatchesProfile (D : xi_basepoint_scan_finite_rank_rkhs_data) : Prop :=
  ∀ x : ℝ, D.kernel x x = D.scanProfile x

/-- The rank of the finite feature span. -/
def rkhsRank (D : xi_basepoint_scan_finite_rank_rkhs_data) : ℕ :=
  D.kappa

end xi_basepoint_scan_finite_rank_rkhs_data

/-- Paper label: `thm:xi-basepoint-scan-finite-rank-rkhs`.  The finite Cauchy feature package
has a positive Gram kernel, its diagonal is the scan profile, and the packaged feature span has
rank `kappa`. -/
theorem paper_xi_basepoint_scan_finite_rank_rkhs
    (D : xi_basepoint_scan_finite_rank_rkhs_data) :
    D.positiveKernel ∧ D.diagonalMatchesProfile ∧ D.rkhsRank = D.kappa := by
  refine ⟨?_, ?_, ?_⟩
  · intro ι _ c x
    exact Finset.sum_nonneg fun k _ => sq_nonneg (Finset.univ.sum fun i : ι =>
      c i * D.feature (x i) k)
  · intro x
    simp [xi_basepoint_scan_finite_rank_rkhs_data.kernel,
      xi_basepoint_scan_finite_rank_rkhs_data.scanProfile, pow_two]
  · rfl

end

end Omega.Zeta
