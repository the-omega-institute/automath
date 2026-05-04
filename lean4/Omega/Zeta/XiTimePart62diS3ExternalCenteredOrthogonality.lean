import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62di-s3-external-centered-orthogonality`. -/
theorem paper_xi_time_part62di_s3_external_centered_orthogonality
    {Gext S3 R : Type*} [Fintype Gext] [Fintype S3] [DecidableEq Gext]
    [DecidableEq S3] [CommSemiring R] (g : S3 -> R) (h : Gext -> R)
    (hg : (Finset.univ.sum fun x : S3 => g x) = 0)
    (hh : (Finset.univ.sum fun x : Gext => h x) = 0) :
    (Finset.univ.sum fun x : Gext × S3 => h x.1 * g x.2) = 0 := by
  classical
  calc
    (Finset.univ.sum fun x : Gext × S3 => h x.1 * g x.2) =
        ∑ x : Gext, ∑ y : S3, h x * g y := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ x : Gext, h x * (∑ y : S3, g y) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [Finset.mul_sum]
    _ = (∑ x : Gext, h x) * (∑ y : S3, g y) := by
      rw [Finset.sum_mul]
    _ = 0 := by
      rw [hh, hg, zero_mul]

end Omega.Zeta
