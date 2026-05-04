import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `cor:conclusion-leyang-external-tower-centered-classfunction-unbiasedness`. -/
theorem paper_conclusion_leyang_external_tower_centered_classfunction_unbiasedness
    {Gext S3 : Type*} [Fintype Gext] [Fintype S3] [DecidableEq Gext] [DecidableEq S3]
    (Phi : Gext → ℝ) (psi : S3 → ℝ)
    (hpsi : (Finset.univ.sum fun τ : S3 => psi τ) = 0) :
    (Finset.univ.sum fun x : Gext => Finset.univ.sum fun τ : S3 => Phi x * psi τ) = 0 := by
  calc
    (Finset.univ.sum fun x : Gext => Finset.univ.sum fun τ : S3 => Phi x * psi τ)
        = Finset.univ.sum fun x : Gext => Phi x * (Finset.univ.sum fun τ : S3 => psi τ) := by
          simp [Finset.mul_sum]
    _ = 0 := by
      simp [hpsi]

end Omega.Conclusion
