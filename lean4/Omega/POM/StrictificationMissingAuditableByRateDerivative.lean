import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-strictification-missing-auditable-by-rate-derivative`.
In the Hellinger endpoint constant model, the derivative observation is the reciprocal endpoint
audit, so dividing the distortion scale by that observation recovers `A^2 - 1`. -/
theorem paper_pom_strictification_missing_auditable_by_rate_derivative
    (A δ derivObs : ℝ) (hA : 1 < A) (hδ : 0 < δ)
    (hobs : derivObs = δ / (A ^ (2 : ℕ) - 1)) :
    δ / derivObs = A ^ (2 : ℕ) - 1 := by
  have hden_pos : 0 < A ^ (2 : ℕ) - 1 := by
    nlinarith [sq_pos_of_ne_zero (show A ≠ 0 by nlinarith)]
  rw [hobs]
  field_simp [hδ.ne', hden_pos.ne']

end Omega.POM
