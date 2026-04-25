import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-pw-holonomy-fill-linear-bound`. A finite chain-cochain pairing is
bounded by the coefficient l1 norm times the pointwise label bound, and hence by any larger
filling budget. -/
theorem paper_pom_pw_holonomy_fill_linear_bound {n : ℕ} (coeff label : Fin n → ℝ)
    (aNorm sigmaNorm anomNorm fill : ℝ)
    (hanom : anomNorm = |∑ i, coeff i * label i|) (hlabel : ∀ i, |label i| ≤ aNorm)
    (hsigma : sigmaNorm = ∑ i, |coeff i|) (hfill : sigmaNorm ≤ fill)
    (haNonneg : 0 ≤ aNorm) : anomNorm ≤ aNorm * fill := by
  rw [hanom]
  calc
    |∑ i, coeff i * label i| ≤ ∑ i, |coeff i * label i| := by
      simpa using
        (Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (f := fun i : Fin n => coeff i * label i))
    _ = ∑ i, |coeff i| * |label i| := by
      simp [abs_mul]
    _ ≤ ∑ i, |coeff i| * aNorm := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlabel i) (abs_nonneg _)
    _ = sigmaNorm * aNorm := by
      rw [hsigma]
      exact (Finset.sum_mul Finset.univ (fun i : Fin n => |coeff i|) aNorm).symm
    _ = aNorm * sigmaNorm := by ring
    _ ≤ aNorm * fill := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hfill haNonneg

end Omega.POM
